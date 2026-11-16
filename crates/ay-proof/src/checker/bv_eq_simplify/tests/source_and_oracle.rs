// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::fmt::Write as _;
use std::process::Stdio;
use std::time::Duration;
use wait_timeout::ChildExt as _;

#[test]
fn a_source_alias_needs_its_authored_premise_and_explicit_congruence() {
    let (mut terms, mut proof, source, _) = refutation(64);
    // Start with the common-base proof's canonical false equality, then
    // replace only the problem's right-hand base by an independent word.
    let TermData::App(_, canonical_sides) = terms.get(source) else {
        panic!("equality")
    };
    let (left, right) = (canonical_sides[0], canonical_sides[1]);
    let x = terms.mk_var("x", Sort::bitvec(64));
    let y = terms.mk_var("y", Sort::bitvec(64));
    let zero = terms.mk_bitvec(0.into(), 64);
    let other_right = add(&mut terms, y, zero, 64);
    let original = eq(&mut terms, left, other_right);
    let invented = claim(&mut terms, original, false);
    assert!(
        !accepted(&terms, invented),
        "an unproved alias is not algebra"
    );

    // Recover the already checked canonical guard unit before its final
    // resolution. The canonical assumption and its final use are discarded.
    proof.steps.pop();
    proof.steps[0] = ay_core::ProofStep::Assume(original);
    let base = eq(&mut terms, x, y);
    let base_unit = proof.add_assume(base, None);
    let lifted = eq(&mut terms, right, other_right);
    let lift = proof.add_rule_step(AletheRule::Cong, vec![lifted], vec![base_unit], vec![]);
    let equivalent = eq(&mut terms, source, original);
    let equivalent_unit =
        proof.add_rule_step(AletheRule::Cong, vec![equivalent], vec![lift], vec![]);
    let not_equivalent = terms.mk_not_raw(equivalent);
    let not_original = terms.mk_not_raw(original);
    let bridge = proof.add_rule_step(
        AletheRule::EquivPos1,
        vec![not_equivalent, source, not_original],
        vec![],
        vec![],
    );
    let bridge = proof.add_resolution(
        vec![source, not_original],
        equivalent,
        equivalent_unit,
        bridge,
    );
    let guard = proof.add_resolution(vec![not_original], source, bridge, ProofId(5));
    proof.add_resolution(vec![], original, ProofId(0), guard);
    crate::check_proof_strict_with_context(&proof, &terms, None, None, Some(&[original, base]))
        .expect("the complete source alias is explicitly lifted");
    assert!(
        crate::check_proof_strict_with_context(&proof, &terms, None, None, Some(&[original]))
            .is_err(),
        "a base equality absent after pop cannot remain a source assumption"
    );
    let mut missing = proof.clone();
    let ay_core::ProofStep::Step { premises, .. } = &mut missing.steps[7] else {
        panic!("congruence")
    };
    premises.clear();
    assert!(crate::check_proof_strict_with_context(
        &missing,
        &terms,
        None,
        None,
        Some(&[original, base])
    )
    .is_err());
}

#[test]
fn exhaustive_offset_truth_agrees_with_the_independent_z3_reference() {
    let Some(oracle) = ay_test_support::z3::optional_z3("bv_eq_simplify") else {
        return;
    };
    let directory = std::env::var("AY_BV_EQ_SIMPLIFY_ARTIFACT_DIR")
        .map(std::path::PathBuf::from)
        .unwrap_or_else(|_| {
            std::env::temp_dir().join(format!("ay-bv-eq-z3-{}", std::process::id()))
        });
    std::fs::create_dir_all(&directory).expect("owned oracle artifact directory");
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
                // Ask whether any interpretation refutes the exact Boolean
                // equality admitted by the native rule, then its false twin.
                let source = format!("(= (bvadd x (_ bv{a} {width})) (bvadd x (_ bv{b} {width})))");
                for truth in [a == b, a != b] {
                    writeln!(
                        script,
                        "(push 1)\n(assert (not (= {source} {truth})))\n(check-sat)\n(pop 1)"
                    )
                    .unwrap();
                    expected.push(if truth == (a == b) { "unsat" } else { "sat" });
                }
            }
        }
        script.push_str("(reset)\n");
    }
    let input = directory.join("exhaustive-small-offsets.smt2");
    std::fs::write(&input, &script).expect("write exact oracle input");
    let stdout = std::fs::File::create(directory.join("exhaustive-small-offsets.stdout")).unwrap();
    let stderr = std::fs::File::create(directory.join("exhaustive-small-offsets.stderr")).unwrap();
    let mut child = oracle
        .command()
        .args(["-T:30", "-memory:2048"])
        .arg(&input)
        .stdout(Stdio::from(stdout))
        .stderr(Stdio::from(stderr))
        .spawn()
        .expect("spawn identified oracle");
    let status = match child
        .wait_timeout(Duration::from_secs(30))
        .expect("bounded oracle wait")
    {
        Some(status) => status,
        None => {
            child.kill().expect("kill only the child this test started");
            let _ = child.wait();
            panic!("reference oracle timed out without evidence");
        }
    };
    assert!(status.success());
    let output =
        std::fs::read_to_string(directory.join("exhaustive-small-offsets.stdout")).unwrap();
    let answers: Vec<_> = output
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty())
        .collect();
    assert_eq!(answers, expected, "oracle={}\n{output}", oracle.identity());
    assert_eq!(
        std::fs::read(directory.join("exhaustive-small-offsets.stderr")).unwrap(),
        Vec::<u8>::new()
    );
}
