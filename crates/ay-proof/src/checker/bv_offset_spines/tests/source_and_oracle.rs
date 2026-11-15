// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::{fmt::Write as _, process::Stdio, time::Duration};
use wait_timeout::ChildExt as _;

#[test]
fn bv_offset_spines_aliases_need_authored_earlier_congruence_and_transitivity() {
    let (mut t, _, _, left) = fixture(64);
    let x = t.mk_var("x", Sort::bitvec(64));
    let y = t.mk_var("y", Sort::bitvec(64));
    let z = t.mk_var("z", Sort::bitvec(64));
    let left = frame(&mut t, left, 3, 64, 0);
    let canonical = frame(&mut t, x, 3, 64, 0);
    let target = frame(&mut t, y, 3, 64, 0);
    let identity = eq(&mut t, left, canonical);
    let goal = eq(&mut t, left, target);
    let denied = t.mk_not_raw(goal);
    let invented = claim(&mut t, goal, true);
    assert!(!accepted(&t, invented));
    let alias = eq(&mut t, x, y);
    let foreign_alias = eq(&mut t, x, z);
    let mut p = Proof::new();
    let assumed = p.add_assume(denied, None);
    let alias_unit = p.add_assume(alias, None);
    let canonical_unit = derive(&mut t, &mut p, identity, true).0;
    let transport = eq(&mut t, canonical, target);
    let congruence = p.add_rule_step(AletheRule::Cong, vec![transport], vec![alias_unit], vec![]);
    let conclusion = p.add_rule_step(
        AletheRule::Trans,
        vec![goal],
        vec![canonical_unit, congruence],
        vec![],
    );
    p.add_resolution(vec![], goal, assumed, conclusion);
    crate::check_proof_strict_with_context(&p, &t, None, None, Some(&[denied, alias])).unwrap();
    // Missing, removed-after-pop, and a different source's alias all fail at
    // the existing authored-assumption boundary; no new alias semantics exist.
    for assertions in [vec![denied], vec![denied, foreign_alias]] {
        assert!(
            crate::check_proof_strict_with_context(&p, &t, None, None, Some(&assertions)).is_err()
        );
    }
    let mut active_assertions = vec![denied];
    active_assertions.push(alias);
    crate::check_proof_strict_with_context(&p, &t, None, None, Some(&active_assertions)).unwrap();
    active_assertions.pop();
    assert!(
        crate::check_proof_strict_with_context(&p, &t, None, None, Some(&active_assertions))
            .is_err()
    );
    for premises in [vec![], vec![ProofId((p.steps.len() - 1) as u32)]] {
        let mut invalid = p.clone();
        let ProofStep::Step {
            premises: actual, ..
        } = &mut invalid.steps[congruence.0 as usize]
        else {
            panic!("congruence")
        };
        *actual = premises;
        assert!(crate::check_proof_strict_with_context(
            &invalid,
            &t,
            None,
            None,
            Some(&[denied, alias])
        )
        .is_err());
    }
    let text = export(&t, &p, &[denied, alias]);
    let declarations="(set-logic QF_BV)\n(declare-const x (_ BitVec 64))\n(declare-const y (_ BitVec 64))\n(declare-const z (_ BitVec 64))\n";
    let original = format!(
        "{declarations}(assert {})\n(assert {})\n(check-sat)\n",
        crate::format_term_alethe(&t, denied),
        crate::format_term_alethe(&t, alias)
    );
    artifacts("alias-present", &original, &text, None);
    let missing = format!(
        "{declarations}(assert {})\n(check-sat)\n",
        crate::format_term_alethe(&t, denied)
    );
    artifacts("alias-missing", &missing, &text, None);
    artifacts("alias-popped", &missing, &text, None);
    let foreign = format!(
        "{declarations}(assert {})\n(assert {})\n(check-sat)\n",
        crate::format_term_alethe(&t, denied),
        crate::format_term_alethe(&t, foreign_alias)
    );
    artifacts("alias-foreign-source", &foreign, &text, None);
}

#[test]
fn bv_offset_spines_exhaustive_and_exact_plan_agree_with_pinned_z3() {
    let Some(oracle) = ay_test_support::z3::optional_z3("bv_offset_spines") else {
        return;
    };
    let directory = std::env::var("AY_BV_OFFSET_SPINES_ARTIFACT_DIR")
        .map(std::path::PathBuf::from)
        .unwrap_or_else(|_| {
            std::env::temp_dir().join(format!("ay-bv-spines-z3-{}", std::process::id()))
        });
    std::fs::create_dir_all(&directory).unwrap();
    let mut script = String::new();
    let mut expected = Vec::new();
    for width in 1..=4 {
        let modulus = 1u128 << width;
        writeln!(
            script,
            "(set-logic QF_BV)\n(declare-const x (_ BitVec {width}))"
        )
        .unwrap();
        for a in 0..modulus {
            for b in 0..modulus {
                for c in 0..modulus {
                    let truth = (a + modulus - b) % modulus == c;
                    let theorem=format!("(= (bvsub (bvadd x (_ bv{a} {width})) (_ bv{b} {width})) (bvadd x (_ bv{c} {width})))");
                    for result in [truth, !truth] {
                        writeln!(
                            script,
                            "(push 1)\n(assert (not (= {theorem} {result})))\n(check-sat)\n(pop 1)"
                        )
                        .unwrap();
                        expected.push(if result == truth { "unsat" } else { "sat" });
                    }
                }
            }
        }
        script.push_str("(reset)\n");
    }
    let plan: serde_json::Value =
        serde_json::from_str(include_str!("canonical-plan-obligations.json")).unwrap();
    let mut t = TermStore::new();
    script.push_str("(set-logic QF_BV)\n(declare-const frame_entry_sp (_ BitVec 64))\n(declare-const frame_exit_0_resume_sp (_ BitVec 64))\n");
    for row in plan["normalizations"].as_array().unwrap() {
        let left = from_plan(&mut t, &row["left"]);
        let right = from_plan(&mut t, &row["right"]);
        let source = eq(&mut t, left, right);
        let checked_claim = claim(&mut t, source, true);
        assert!(accepted(&t, checked_claim));
        let theorem = crate::format_term_alethe(&t, source);
        for result in [true, false] {
            writeln!(
                script,
                "(push 1)\n(assert (not (= {theorem} {result})))\n(check-sat)\n(pop 1)"
            )
            .unwrap();
            expected.push(if result { "unsat" } else { "sat" });
        }
    }
    script.push_str("(reset)\n");
    for width in [1, 8, 64, 128] {
        let (t, source, _, _) = fixture(width);
        let theorem = crate::format_term_alethe(&t, source);
        writeln!(
            script,
            "(set-logic QF_BV)\n(declare-const x (_ BitVec {width}))"
        )
        .unwrap();
        for result in [true, false] {
            writeln!(
                script,
                "(push 1)\n(assert (not (= {theorem} {result})))\n(check-sat)\n(pop 1)"
            )
            .unwrap();
            expected.push(if result { "unsat" } else { "sat" });
        }
        script.push_str("(reset)\n");
    }
    let input = directory.join("offset-spines-z3.smt2");
    std::fs::write(&input, &script).unwrap();
    let stdout = std::fs::File::create(directory.join("offset-spines-z3.stdout")).unwrap();
    let stderr = std::fs::File::create(directory.join("offset-spines-z3.stderr")).unwrap();
    let mut child = oracle
        .command()
        .args(["-T:30", "-memory:2048"])
        .arg(&input)
        .stdout(Stdio::from(stdout))
        .stderr(Stdio::from(stderr))
        .spawn()
        .unwrap();
    let status = match child.wait_timeout(Duration::from_secs(30)).unwrap() {
        Some(status) => status,
        None => {
            child.kill().unwrap();
            let _ = child.wait();
            panic!("pinned Z3 timed out; no oracle evidence")
        }
    };
    assert!(status.success());
    let output = std::fs::read_to_string(directory.join("offset-spines-z3.stdout")).unwrap();
    let actual: Vec<_> = output
        .lines()
        .map(str::trim)
        .filter(|l| !l.is_empty())
        .collect();
    assert_eq!(actual, expected, "oracle={}\n{output}", oracle.identity());
    assert!(std::fs::read(directory.join("offset-spines-z3.stderr"))
        .unwrap()
        .is_empty());
    std::fs::write(directory.join("offset-spines-z3-receipt.json"),serde_json::to_vec_pretty(&serde_json::json!({"oracle":oracle.identity(),"queries":expected.len(),"unsat":expected.iter().filter(|x|**x=="unsat").count(),"sat":expected.iter().filter(|x|**x=="sat").count(),"unknown":0})).unwrap()).unwrap();
}
