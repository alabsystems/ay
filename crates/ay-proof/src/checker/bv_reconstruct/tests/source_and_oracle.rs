// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::{fmt::Write as _, process::Stdio, time::Duration};
use wait_timeout::ChildExt as _;

fn partitions(width: u32) -> Vec<Vec<(u32, u32)>> {
    let mut results = Vec::new();
    for cuts in 0..(1u32 << (width - 1)) {
        let mut ranges = Vec::new();
        let mut low = 0;
        for high in 0..width {
            if high + 1 == width || cuts & (1 << high) != 0 {
                ranges.push((low, high + 1 - low));
                low = high + 1;
            }
        }
        results.push(ranges);
    }
    results
}
fn permutations(xs: &mut [(u32, u32)], at: usize, out: &mut Vec<Vec<(u32, u32)>>) {
    if at == xs.len() {
        out.push(xs.to_vec());
        return;
    }
    for i in at..xs.len() {
        xs.swap(at, i);
        permutations(xs, at + 1, out);
        xs.swap(at, i);
    }
}
/// An independent concrete test interpreter; checker masks/coverage are not used.
fn value(t: &TermStore, term: TermId, word: TermId, bits: u128) -> u128 {
    if term == word {
        return bits;
    }
    let width = t.sort(term).bitvec_width().unwrap();
    let modulus_mask = u128::MAX >> (128 - width);
    match t.get(term) {
        TermData::Const(Constant::BitVec { value, .. }) => value.to_u128().unwrap(),
        TermData::App(Symbol::Named(op), args) if op == "bvor" => {
            value(t, args[0], word, bits) | value(t, args[1], word, bits)
        }
        TermData::App(Symbol::Named(op), args) if op == "bvshl" => {
            (value(t, args[0], word, bits) << value(t, args[1], word, bits)) & modulus_mask
        }
        TermData::App(Symbol::Indexed(op, _), args) if op == "zero_extend" => {
            value(t, args[0], word, bits)
        }
        TermData::App(Symbol::Indexed(op, indices), args) if op == "extract" => {
            (value(t, args[0], word, bits) >> indices[1]) & modulus_mask
        }
        _ => panic!("reference grammar"),
    }
}

#[test]
fn bv_reconstruct_exhaustive_small_width_partitions_orders_values() {
    let mut count = 0;
    for width in 1..=5 {
        for mut ranges in partitions(width) {
            let mut orders = Vec::new();
            permutations(&mut ranges, 0, &mut orders);
            for order in orders {
                let mut t = TermStore::new();
                let word = t.mk_var("x", Sort::bitvec(width));
                let pack = packed(&mut t, word, width, &order, false);
                let source = eq(&mut t, pack, word);
                assert!(accepts(&t, source));
                for bits in 0..(1u128 << width) {
                    assert_eq!(value(&t, pack, word, bits), bits);
                }
                check_and_export(&mut t, source, width, &format!("small-{width}-{count:04}"));
                count += 1;
            }
        }
    }
    assert_eq!(count, 325);
}

#[test]
fn bv_reconstruct_aliases_need_earlier_congruence_transitivity_and_active_source() {
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::bitvec(8));
    let y = t.mk_var("y", Sort::bitvec(8));
    let z = t.mk_var("z", Sort::bitvec(8));
    let px = packed(&mut t, x, 8, &[(0, 4), (4, 4)], false);
    let py = packed(&mut t, y, 8, &[(0, 4), (4, 4)], false);
    let source = eq(&mut t, px, x);
    let target = eq(&mut t, px, y);
    assert!(!accepts(&t, target));
    let alias = eq(&mut t, x, y);
    let foreign = eq(&mut t, x, z);
    let denied = t.mk_not_raw(target);
    let mut p = Proof::new();
    let a = p.add_assume(denied, None);
    let alias_unit = p.add_assume(alias, None);
    let unit = p.add_rule_step(AletheRule::BvReconstructV1, vec![source], vec![], vec![]);
    let target_unit = p.add_rule_step(
        AletheRule::Trans,
        vec![target],
        vec![unit, alias_unit],
        vec![],
    );
    p.add_resolution(vec![], target, a, target_unit);
    crate::check_proof_strict_with_context(&p, &t, None, None, Some(&[denied, alias])).unwrap();
    let text = export(&t, &p, &[denied, alias]);
    let declarations="(set-logic QF_BV)\n(declare-const x (_ BitVec 8))\n(declare-const y (_ BitVec 8))\n(declare-const z (_ BitVec 8))\n";
    let authored = format!(
        "{declarations}(assert {})\n",
        crate::format_term_alethe(&t, denied)
    );
    artifact(
        "alias-present",
        &format!(
            "{authored}(assert {})\n(check-sat)\n",
            crate::format_term_alethe(&t, alias)
        ),
        &text,
    );
    for (name, extra, active) in [
        ("alias-missing", String::new(), vec![denied]),
        ("alias-popped", String::new(), vec![denied]),
        (
            "alias-foreign",
            format!("(assert {})\n", crate::format_term_alethe(&t, foreign)),
            vec![denied, foreign],
        ),
    ] {
        assert!(crate::check_proof_strict_with_context(&p, &t, None, None, Some(&active)).is_err());
        artifact(name, &format!("{authored}{extra}(check-sat)\n"), &text);
    }
    // Congruence is ordinary ownership of transport through the pack, never
    // an implicit alias feature of the new primitive.
    let full_x = indexed(&mut t, "zero_extend", vec![0], x, 8);
    let full_y = indexed(&mut t, "zero_extend", vec![0], y, 8);
    let canonical = eq(&mut t, full_x, x);
    let transport = eq(&mut t, full_x, full_y);
    let goal = eq(&mut t, full_y, x);
    let denied = t.mk_not_raw(goal);
    let mut p = Proof::new();
    let a = p.add_assume(denied, None);
    let alias_unit = p.add_assume(alias, None);
    let c = p.add_rule_step(AletheRule::Cong, vec![transport], vec![alias_unit], vec![]);
    let reversed = eq(&mut t, full_y, full_x);
    let c = p.add_rule_step(AletheRule::Symm, vec![reversed], vec![c], vec![]);
    let u = p.add_rule_step(AletheRule::BvReconstructV1, vec![canonical], vec![], vec![]);
    let u = p.add_rule_step(AletheRule::Trans, vec![goal], vec![c, u], vec![]);
    p.add_resolution(vec![], goal, a, u);
    crate::check_proof_strict_with_context(&p, &t, None, None, Some(&[denied, alias])).unwrap();
    let _ = py;
}

#[test]
fn bv_reconstruct_pinned_z3_checks_exhaustive_shapes_originals_and_causal_defects() {
    let Some(oracle) = ay_test_support::z3::optional_z3("bv_reconstruct") else {
        return;
    };
    let mut script = String::new();
    let mut expected = Vec::new();
    for width in 1..=5 {
        writeln!(script,"(set-logic QF_BV)\n(declare-const x (_ BitVec {width}))\n(declare-const y (_ BitVec {width}))").unwrap();
        for mut ranges in partitions(width) {
            let mut orders = Vec::new();
            permutations(&mut ranges, 0, &mut orders);
            for order in orders {
                let mut t = TermStore::new();
                let word = t.mk_var("x", Sort::bitvec(width));
                let y = t.mk_var("y", Sort::bitvec(width));
                let pack = packed(&mut t, word, width, &order, false);
                let source = eq(&mut t, pack, word);
                let wrong = eq(&mut t, pack, y);
                for (source, answer) in [(source, "unsat"), (wrong, "sat")] {
                    writeln!(
                        script,
                        "(push 1)\n(assert (not {}))\n(check-sat)\n(pop 1)",
                        crate::format_term_alethe(&t, source)
                    )
                    .unwrap();
                    expected.push(answer);
                }
            }
        }
        script.push_str("(reset)\n");
    }

    for width in [1, 8, 64, 128] {
        let mut t = TermStore::new();
        let x = t.mk_var("x", Sort::bitvec(width));
        let y = t.mk_var("y", Sort::bitvec(width));
        let ranges: Vec<_> = (0..width).map(|lo| (lo, 1)).collect();
        let pack = packed(&mut t, x, width, &ranges, true);
        let correct = eq(&mut t, pack, x);
        let wrong = eq(&mut t, pack, y);
        writeln!(script,"(set-logic QF_BV)\n(declare-const x (_ BitVec {width}))\n(declare-const y (_ BitVec {width}))").unwrap();
        for (claim, verdict) in [(correct, "unsat"), (wrong, "sat")] {
            writeln!(
                script,
                "(push 1)\n(assert (not {}))\n(check-sat)\n(pop 1)",
                crate::format_term_alethe(&t, claim)
            )
            .unwrap();
            expected.push(verdict);
        }
        script.push_str("(reset)\n");
    }
    let originals: serde_json::Value =
        serde_json::from_str(include_str!("ten-packing-identities.json")).unwrap();
    for row in originals.as_array().unwrap() {
        let word = row["word"].as_str().unwrap();
        let source = row["pure_packing_equality"].as_str().unwrap();
        writeln!(script,"(set-logic QF_BV)\n(declare-const {word} (_ BitVec 64))\n(assert (not {source}))\n(check-sat)\n(reset)").unwrap();
        expected.push("unsat");
    }
    let directory = std::env::var("AY_BV_RECONSTRUCT_ARTIFACT_DIR")
        .map(std::path::PathBuf::from)
        .unwrap_or_else(|_| {
            std::env::temp_dir().join(format!("bv-reconstruct-z3-{}", std::process::id()))
        });
    std::fs::create_dir_all(&directory).unwrap();
    let path = directory.join("pinned-z3.smt2");
    std::fs::write(&path, &script).unwrap();
    let mut child = oracle
        .command()
        .args(["-T:30", "-memory:2048"])
        .arg(&path)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    let Some(status) = child.wait_timeout(Duration::from_secs(40)).unwrap() else {
        child.kill().unwrap();
        panic!("bounded oracle timeout");
    };
    let output = child.wait_with_output().unwrap();
    assert!(status.success());
    assert!(
        output.stderr.is_empty(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let text = String::from_utf8(output.stdout).unwrap();
    std::fs::write(directory.join("pinned-z3.stdout"), &text).unwrap();
    let actual: Vec<_> = text.lines().collect();
    assert_eq!(actual, expected);
}
