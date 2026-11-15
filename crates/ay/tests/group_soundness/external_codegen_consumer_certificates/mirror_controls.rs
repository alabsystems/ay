// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The consumer-rule mirror's own controls: every mirrored rule refuses its
//! control step edited, and accepts it unedited; a certificate is counted as
//! checked only when every one of its commands was decided and accepted; and
//! the measured defects stay refused.
//!
//! REGRESSION (measured 2026-09-30 on 57cef15fd/c57bd8481): the mirror read
//! `bitblast_ashr`, `and_simplify` and `or_simplify` steps only and passed
//! every other step unread, yet the corpus doc said every certificate was
//! "checked against the consumer's rules as mirrored here"; a
//! `bitblast_udiv`/`bitblast_urem` step was never read. On that mirror every
//! edited control below except those three rules' is passed.

use super::consumer_rules::{
    consumer_rule_defects, mirror_certificate, mirrored_rules, pinned_refused_ashr_steps,
    pinned_refused_divider_steps, pinned_refused_zero_extend_steps, step_verdict,
};

#[path = "mirror_controls/table.rs"]
mod table;
use table::{Control, CONTROLS};

const DECLARATIONS: &str = "(set-logic ALL)\n(declare-const p Bool)\n(declare-const q Bool)\n\
    (declare-const r Bool)\n(declare-const s Bool)\n(declare-const a Bool)\n(declare-const b Bool)\n\
    (declare-const c Bool)\n(declare-const d Bool)\n(declare-const m (Array Bool Bool))\n";

/// The control as a whole certificate: the problem asserts `false` (and what
/// the control's assumptions cite), and the proof ends refuting it.
fn certificate(control: &Control, steps: &str) -> (String, String) {
    let mut problem = DECLARATIONS.to_string();
    for assertion in control.assertions {
        problem.push_str(&format!("(assert {assertion})\n"));
    }
    problem.push_str("(assert false)\n(check-sat)\n");
    let proof = format!(
        "(assume e.a false)\n{steps}\n(step e.f (cl (not false)) :rule false)\n\
         (step e.e (cl) :rule resolution :premises (e.a e.f))\n"
    );
    (problem, proof)
}

/// The control with its edit applied to its last command, the rule's step.
fn edited(control: &Control) -> String {
    let at = control.steps.rfind('\n').map_or(0, |i| i + 1);
    let (head, step) = control.steps.split_at(at);
    let (from, to) = control.edit;
    assert!(
        step.contains(from),
        "{}: the edit does not apply",
        control.rule
    );
    format!("{head}{}", step.replacen(from, to, 1))
}

/// Every edited control is refused at its step by the mirror's rule.
#[test]
fn every_mirrored_rule_refuses_its_edited_control() {
    let mut passed = Vec::new();
    for control in CONTROLS {
        let (_, proof) = certificate(control, &edited(control));
        let defects = consumer_rule_defects(&proof);
        let prefix = format!("step t ({})", control.rule);
        if !defects.iter().any(|defect| defect.starts_with(&prefix)) {
            passed.push(format!("{}: {defects:?}", control.rule));
        }
        let (_, proof) = certificate(control, control.steps);
        assert_eq!(
            consumer_rule_defects(&proof),
            Vec::<String>::new(),
            "{}",
            control.rule
        );
    }
    assert!(
        passed.is_empty(),
        "edited controls the mirror passes:\n{}",
        passed.join("\n")
    );
}

/// `CLEAN_PATH`'s verdict on a control certificate, when one is configured.
fn clean_accepts(problem: &str, proof: &str) -> Option<bool> {
    let checker = std::env::var_os("CLEAN_PATH")?;
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("cert.json");
    let json = serde_json::json!({
        "type": "alethe_certificate", "version": "1.0", "problem": problem, "proof": proof,
    });
    std::fs::write(&path, serde_json::to_vec(&json).expect("json")).expect("write cert");
    let output = std::process::Command::new(checker)
        .args(["cert", "verify-external"])
        .arg(&path)
        .arg("--verbose")
        .output()
        .expect("run clean");
    let stdout = String::from_utf8_lossy(&output.stdout).to_lowercase();
    Some(
        output.status.success()
            && stdout.contains("external certificate verification: passed")
            && stdout.contains("proof status: fully verified"),
    )
}

/// Every control is decided: accepted unedited (the whole certificate is
/// checked), refused edited at its step; and, with `CLEAN_PATH`, the
/// consumer agrees on both.
#[test]
fn every_mirrored_rule_accepts_its_control_and_the_consumer_agrees() {
    let mut failures = Vec::new();
    let mut replayed = 0;
    for control in CONTROLS {
        let (problem, valid) = certificate(control, control.steps);
        let coverage = mirror_certificate(&problem, &valid);
        if !coverage.checked() {
            failures.push(format!(
                "{}: not checked: {:?} {:?}",
                control.rule, coverage.refused, coverage.undetermined
            ));
        }
        let (_, invalid) = certificate(control, &edited(control));
        let verdict = step_verdict(&problem, &invalid, "t").unwrap_or_default();
        if !verdict.starts_with("refused") {
            failures.push(format!("{}: the edited step is {verdict}", control.rule));
        }
        if let (Some(accepts), Some(refuses)) = (
            clean_accepts(&problem, &valid),
            clean_accepts(&problem, &invalid),
        ) {
            replayed += 1;
            if !accepts || refuses {
                failures.push(format!(
                    "{}: CLEAN_PATH accepts the control: {accepts}, the edit: {refuses}",
                    control.rule
                ));
            }
        }
    }
    eprintln!(
        "mirror controls: {} rules, {replayed} replayed through CLEAN_PATH",
        CONTROLS.len()
    );
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// The covered-rule set is the dispatch table, and each of its rules has a
/// control.
#[test]
fn every_mirrored_rule_has_a_control() {
    let mut mirrored: Vec<&str> = mirrored_rules().collect();
    let mut controlled: Vec<&str> = CONTROLS.iter().map(|control| control.rule).collect();
    mirrored.sort_unstable();
    controlled.sort_unstable();
    assert_eq!(mirrored, controlled);
}

/// A certificate counts as checked only when every command was decided: one
/// step of a rule the mirror does not model (`ac_simp`), or a step whose
/// operand width it cannot infer, leaves the certificate not independently
/// checked, though nothing is refused.
#[test]
fn a_certificate_is_checked_only_when_every_step_is_mirrored() {
    let udiv = CONTROLS
        .iter()
        .find(|control| control.rule == "bitblast_udiv")
        .expect("udiv");
    let (problem, proof) = certificate(udiv, udiv.steps);
    assert!(mirror_certificate(&problem, &proof).checked());
    for (rule, extra) in [
        ("ac_simp", "(step x (cl (= (and p p) p)) :rule ac_simp)"),
        (
            "bitblast_var",
            "(step x (cl (= y (@bbterm ((_ @bit_of 0) y)))) :rule bitblast_var)",
        ),
    ] {
        let (problem, proof) = certificate(udiv, &format!("{extra}\n{}", udiv.steps));
        let coverage = mirror_certificate(&problem, &proof);
        assert!(!coverage.checked(), "{rule}: counted as checked");
        assert!(
            coverage.refused.is_empty(),
            "{rule}: {:?}",
            coverage.refused
        );
        assert!(
            coverage.undetermined.contains_key(rule),
            "{rule}: {:?}",
            coverage.undetermined
        );
    }
}

/// The measured defects, spelled by hand: the dialect classifiers, and the
/// consumer's `and_simplify`/`or_simplify` over a nested connective.
#[test]
fn consumer_rule_mirrors_refuse_the_measured_defects() {
    // Zero-filled overshift (AY c6a80496e, `Peephole: ASR Bd, Bn, #0`): the
    // sign fill is what pinned Carcara refuses, unless the sign bit is
    // literally `false` (both checkers then build the same term).
    let zero_fill = "\
(define-fun g () Bool (ite y ((_ @bit_of 1) x) false))
(define-fun h () Bool (ite y ((_ @bit_of 0) x) false))
(step s (cl (= (bvashr (@bbterm ((_ @bit_of 0) x) ((_ @bit_of 1) x)) (@bbterm false false)) (@bbterm h g))) :rule bitblast_ashr)
";
    let sign_fill = zero_fill.replace(" false))\n", " ((_ @bit_of 1) x)))\n");
    assert_eq!(pinned_refused_ashr_steps(&sign_fill), vec!["s".to_string()]);
    assert_eq!(pinned_refused_ashr_steps(zero_fill), Vec::<String>::new());
    let non_negative =
        zero_fill.replace("((_ @bit_of 1) x)) (@bbterm false", "false) (@bbterm false");
    assert_eq!(
        pinned_refused_ashr_steps(&non_negative),
        Vec::<String>::new()
    );

    // `zero_extend` checked as `concat` (`refl`, or `cong` from a named word)
    // is what pinned Carcara refuses; a `cong` between two extensions is not.
    let zero_extend = "\
(define-fun w () (_ BitVec 6) ((_ zero_extend 2) x))
(step r (cl (= ((_ zero_extend 2) x) (concat (_ bv0 2) x))) :rule refl)
(step z (cl (= ((_ zero_extend 0) x) x)) :rule refl)
(step c (cl (= w (concat (@bbterm false false) x))) :rule cong)
(step k (cl (= ((_ zero_extend 2) x) ((_ zero_extend 2) y))) :rule cong)
";
    assert_eq!(
        pinned_refused_zero_extend_steps(zero_extend),
        ["r", "z", "c"]
    );

    // A default-dialect divider step is Clean's long division, which pinned
    // Carcara refuses unless the dividend is literally zero (both circuits
    // then build the same terms); the shift it is checked against is not.
    let divider = "\
(define-fun w () (_ BitVec 2) (@bbterm false false))
(step q (cl (= (bvudiv (@bbterm a b) (@bbterm false true)) (@bbterm c d))) :rule bitblast_udiv)
(step m (cl (= (bvurem (@bbterm false b) (@bbterm false true)) (@bbterm e f))) :rule bitblast_urem)
(step z (cl (= (bvudiv (@bbterm false false) (@bbterm a b)) (@bbterm g h))) :rule bitblast_udiv)
(step n (cl (= (bvurem w (@bbterm a b)) (@bbterm false false))) :rule bitblast_urem)
(step s (cl (= (bvlshr (@bbterm a b) (@bbterm true false)) (@bbterm b false))) :rule bitblast_lshr)
";
    assert_eq!(pinned_refused_divider_steps(divider), ["q", "m"]);

    // `(= (and true X) X)` with X a conjunction, bare and behind a name.
    let nested = "\
(define-fun n () Bool (and a b))
(step s1 (cl (= (and true (and a b)) (and a b))) :rule and_simplify)
(step s2 (cl (= (and true n) n)) :rule and_simplify)
(step s3 (cl (= (or (or c d) false) (or c d))) :rule or_simplify)
";
    assert_eq!(consumer_rule_defects(nested).len(), 3);
    let unwrapped = "\
(define-fun n () Bool (and a b))
(step s1 (cl (= (and true n) (and n))) :rule and_simplify)
(step s2 (cl (= (and n) n)) :rule and_simplify)
(step s3 (cl (= (and true a) a)) :rule and_simplify)
(step s4 (cl (= (and a true b) (and a b))) :rule and_simplify)
(step s5 (cl (= (or c false (not c)) true)) :rule or_simplify)
";
    assert_eq!(consumer_rule_defects(unwrapped), Vec::<String>::new());
}

/// external-codegen's one-shot argv on `script` (plus `flags`): the verdict and the
/// certificate.
fn one_shot(script: &str, flags: &[&str]) -> (String, String) {
    use crate::spawn::OutputTimeout;
    let dir = tempfile::tempdir().expect("tempdir");
    let (smt2, proof) = (dir.path().join("q.smt2"), dir.path().join("q.alethe"));
    std::fs::write(&smt2, script).expect("write the query");
    let output = std::process::Command::new(env!("CARGO_BIN_EXE_ay"))
        .arg("-smt2")
        .arg(&smt2)
        .args(["--strict-proofs", "--proof"])
        .arg(&proof)
        .args(["--proof-format", "alethe"])
        .args(flags)
        .output_timeout(crate::strict_certificate_publication::QUERY_TIMEOUT)
        .expect("run ay");
    let verdicts = crate::strict_certificate_publication::verdict_lines(&String::from_utf8_lossy(
        &output.stdout,
    ));
    (
        verdicts.join(" "),
        std::fs::read_to_string(&proof).unwrap_or_default(),
    )
}

/// The step `rule` prints first, with the first bit of its result word
/// negated: a circuit no consumer rule builds.
fn negate_a_result_bit(proof: &str, rule: &str) -> (String, String) {
    let marker = format!(":rule {rule}");
    let line = proof
        .lines()
        .find(|line| line.contains(&marker))
        .unwrap_or_else(|| panic!("no {rule} step"));
    let id = line.split_whitespace().nth(1).expect("step id").to_string();
    let at = line.rfind("(@bbterm ").expect("a bit-blasted result") + "(@bbterm ".len();
    let rest = &line[at..];
    let end = if rest.starts_with('(') {
        let mut depth = 0;
        rest.char_indices()
            .find_map(|(i, c)| {
                depth += match c {
                    '(' => 1,
                    ')' => -1,
                    _ => 0,
                };
                (depth == 0).then_some(i + 1)
            })
            .expect("balanced")
    } else {
        rest.find([' ', ')']).expect("an atom")
    };
    let edited = format!("{}(not {}){}", &line[..at], &rest[..end], &rest[end..]);
    (proof.replacen(line, &edited, 1), id)
}

/// The measured case: certificates whose `bitblast_udiv`/`bitblast_urem`
/// steps the mirror never read. AY's real dividers (four-bit, and the byte
/// zero divisor) are now checked step by step, and the same certificate with
/// one result bit of its divider step negated is refused at that step. In the
/// pinned dialect the zero divisor prints pinned Carcara's divider, which the
/// consumer refuses (measured with Clean, 2026-09-30: `checking failed on
/// step 't1.cbb5.bb' with rule 'bitblast_udiv'`), and so does the mirror.
#[test]
#[ntest::timeout(600_000)]
fn real_divider_steps_are_checked_and_an_edited_one_is_refused() {
    let queries = [
        (
            "(declare-const x (_ BitVec 4))\n(assert (bvult x (bvudiv x #x3)))",
            "bitblast_udiv",
        ),
        (
            "(declare-const x (_ BitVec 4))\n(assert (bvult #x2 (bvurem x #x3)))",
            "bitblast_urem",
        ),
        (
            "(declare-const x (_ BitVec 8))\n(assert (not (= (bvudiv x (_ bv0 8)) (_ bv255 8))))",
            "bitblast_udiv",
        ),
    ];
    for (body, rule) in queries {
        let script = format!("(set-logic QF_BV)\n{body}\n(check-sat)\n");
        let (verdict, proof) = one_shot(&script, &[]);
        assert_eq!(verdict, "unsat", "{body}");
        let coverage = mirror_certificate(&script, &proof);
        assert!(
            coverage.checked(),
            "{body}: {:?} {:?}",
            coverage.refused,
            coverage.undetermined
        );
        assert!(coverage.rules.contains_key(rule), "{body}: no {rule} step");
        let (edited, id) = negate_a_result_bit(&proof, rule);
        let prefix = format!("step {id} ({rule})");
        let defects = consumer_rule_defects(&edited);
        assert!(
            defects.iter().any(|defect| defect.starts_with(&prefix)),
            "{body}: {defects:?}"
        );
    }
    let script = format!("(set-logic QF_BV)\n{}\n(check-sat)\n", queries[2].0);
    let (verdict, proof) = one_shot(&script, &["--alethe-dialect", "pinned-carcara"]);
    assert_eq!(verdict, "unsat");
    let refused = mirror_certificate(&script, &proof).refused;
    assert!(
        refused.len() == 1 && refused[0].contains("(bitblast_udiv)"),
        "the pinned divider: {refused:?}"
    );
}

#[path = "mirror_controls/structure.rs"]
mod structure;

#[path = "mirror_controls/problem.rs"]
mod problem;

#[path = "mirror_controls/front_end.rs"]
mod front_end;

#[path = "mirror_controls/overload.rs"]
mod overload;
