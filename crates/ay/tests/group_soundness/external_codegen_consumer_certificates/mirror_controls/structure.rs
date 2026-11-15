// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The walk's own controls: a certificate is checked only when the walk
//! re-derived the empty clause from the problem's assertions, and the
//! consumer's structural checks around a rule (`check_step_core`,
//! `check_discharge_shared`) refuse what Clean refuses.
//!
//! REGRESSION (measured 2026-10-01 on aca0123d5, introduced by 049bfc24e):
//! the walk counted every certificate below marked `pre-fix: checked` as
//! checked step by step, two of them refutations of the satisfiable
//! `(assert (not q))`. Clean 7330fa6c's checker source (Clean 6a916983a's
//! `third-party/carcara` is identical) refuses every refused case here at the
//! named step and accepts every control; with `CLEAN_PATH` this is replayed.

use super::super::consumer_rules::{
    mirror_certificate, mirror_certificate_with_control, step_verdict,
};
use super::{clean_accepts, CONTROLS};

const DECLARATIONS: &str =
    "(set-logic ALL)\n(declare-const q Bool)\n(declare-const p Bool)\n(declare-const x Bool)\n";

/// `(name, assertions, proof, step, expected verdict prefix of that step)`.
type Case = (
    &'static str,
    &'static str,
    &'static str,
    &'static str,
    &'static str,
);

/// Certificates the consumer refuses for their structure.
const REFUSED: &[Case] = &[
    // pre-fix: checked. SAT: `subproof` without `:discharge` exports `q`.
    (
        "undischarged",
        "(assert (not q))",
        "(assume a0 (not q))\n(anchor :step t1)\n(assume t1.h q)\n\
         (step t1.t2 (cl q) :rule reordering :premises (t1.h))\n\
         (step t1 (cl q) :rule subproof)\n\
         (step t2 (cl) :rule resolution :premises (a0 t1))",
        "t1",
        "refused",
    ),
    // pre-fix: checked. SAT: a non-`subproof` end step exports `q`.
    (
        "undischarged_end",
        "(assert (not q))",
        "(assume a0 (not q))\n(anchor :step t1)\n(assume t1.h q)\n\
         (step t1.t2 (cl q) :rule reordering :premises (t1.h))\n\
         (step t1 (cl q) :rule reordering :premises (t1.t2))\n\
         (step t2 (cl) :rule resolution :premises (a0 t1))",
        "t1",
        "refused",
    ),
    // `subproof` discharging one of its two local assumptions.
    (
        "partial_discharge",
        "(assert (not q))",
        "(assume a0 (not q))\n(anchor :step t1)\n(assume t1.h1 q)\n(assume t1.h2 p)\n\
         (step t1.t2 (cl q) :rule reordering :premises (t1.h1))\n\
         (step t1 (cl (not p) q) :rule subproof :discharge (t1.h2))\n\
         (step t2 (cl (not p)) :rule resolution :premises (a0 t1))",
        "t1",
        "refused",
    ),
    // pre-fix: checked. `:discharge` on a rule other than `subproof`.
    (
        "wrongdischarge",
        "(assert p)\n(assert (not p))",
        "(assume a0 p)\n(assume a1 (not p))\n\
         (step t1 (cl p) :rule reordering :premises (a0) :discharge (a0))\n\
         (step t2 (cl) :rule resolution :premises (t1 a1))",
        "t1",
        "refused",
    ),
    // pre-fix: checked. `subproof` ending an anchor with `:args`.
    (
        "ctxsubproof",
        "(assert q)\n(assert (not q))",
        "(assume a0 q)\n(assume a1 (not q))\n(anchor :step t1 :args ((y Bool)))\n\
         (step t1.t2 (cl (= q q)) :rule refl)\n(step t1 (cl (= q q)) :rule subproof)\n\
         (step t2 (cl) :rule resolution :premises (a0 a1))",
        "t1",
        "refused",
    ),
    // pre-fix: t1.t2 accepted. An outer premise mentioning the bound `x`:
    // Clean's premise scoping is not mirrored, so it is undecided.
    (
        "ctxscope",
        "(assert x)\n(assert (not x))",
        "(assume a0 x)\n(assume a1 (not x))\n(anchor :step t1 :args ((x Bool)))\n\
         (step t1.t2 (cl x) :rule reordering :premises (a0))\n\
         (step t1.t3 (cl (= x x)) :rule refl)\n\
         (step t1 (cl (= (forall ((x Bool)) x) (forall ((x Bool)) x))) :rule bind)\n\
         (step t2 (cl) :rule resolution :premises (a0 a1))",
        "t1.t2",
        "undetermined",
    ),
    // SAT: a correctly discharged `subproof` proves only a tautology.
    (
        "discharged_sat",
        "(assert (not q))",
        "(assume a0 (not q))\n(anchor :step t1)\n(assume t1.h q)\n\
         (step t1.t2 (cl q) :rule reordering :premises (t1.h))\n\
         (step t1 (cl (not q) q) :rule subproof :discharge (t1.h))\n\
         (step t2 (cl) :rule resolution :premises (a0 t1))",
        "t2",
        "refused",
    ),
];

/// The same shapes, which the consumer accepts.
const ACCEPTED: &[Case] = &[
    (
        "discharged",
        "(assert (not q))\n(assert q)",
        "(assume a0 (not q))\n(assume a1 q)\n(anchor :step t1)\n(assume t1.h q)\n\
         (step t1.t2 (cl q) :rule reordering :premises (t1.h))\n\
         (step t1 (cl (not q) q) :rule subproof :discharge (h))\n\
         (step t2 (cl q) :rule resolution :premises (a1 t1))\n\
         (step t3 (cl) :rule resolution :premises (a0 t2))",
        "t1",
        "accepted",
    ),
    (
        "wrongdischarge_ctl",
        "(assert p)\n(assert (not p))",
        "(assume a0 p)\n(assume a1 (not p))\n\
         (step t1 (cl p) :rule reordering :premises (a0))\n\
         (step t2 (cl) :rule resolution :premises (t1 a1))",
        "t1",
        "accepted",
    ),
    (
        "ctxsubproof_ctl",
        "(assert q)\n(assert (not q))",
        "(assume a0 q)\n(assume a1 (not q))\n(anchor :step t1)\n\
         (step t1.t2 (cl (= q q)) :rule refl)\n(step t1 (cl (= q q)) :rule subproof)\n\
         (step t2 (cl) :rule resolution :premises (a0 a1))",
        "t1",
        "accepted",
    ),
];

fn problem(assertions: &str) -> String {
    format!("{DECLARATIONS}{assertions}\n(check-sat)\n")
}

/// Every structurally refused certificate is not checked, refused (or, for
/// premise scoping, undecided) at its step; every control is checked; and
/// `CLEAN_PATH` agrees on all of them.
#[test]
fn the_walk_refuses_what_the_consumer_refuses_around_a_rule() {
    let mut failures = Vec::new();
    let mut replayed = 0;
    for &(name, assertions, proof, step, expected) in REFUSED.iter().chain(ACCEPTED) {
        let problem = problem(assertions);
        let coverage = mirror_certificate(&problem, proof);
        let should_check = expected == "accepted";
        if coverage.checked() != should_check {
            failures.push(format!(
                "{name}: checked={} refused={:?} undetermined={:?}",
                coverage.checked(),
                coverage.refused,
                coverage.undetermined
            ));
        }
        let verdict = step_verdict(&problem, proof, step).unwrap_or_default();
        if !verdict.starts_with(expected) {
            failures.push(format!("{name}: step {step} is {verdict}"));
        }
        if let Some(accepts) = clean_accepts(&problem, proof) {
            replayed += 1;
            if accepts != should_check {
                failures.push(format!("{name}: CLEAN_PATH accepts it: {accepts}"));
            }
        }
    }
    eprintln!("walk structure controls: {replayed} replayed through CLEAN_PATH");
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// The empty-clause refutations above are not checked with their
/// assertions dropped.
#[test]
fn no_certificate_is_checked_against_a_problem_without_assertions() {
    let mut failures = Vec::new();
    for &(name, assertions, proof, ..) in ACCEPTED {
        let coverage = mirror_certificate_with_control(&problem(assertions), proof);
        if !coverage.checked() {
            failures.push(format!("{name}: {:?}", coverage.refused));
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// `steps` with the conclusion of its last step, `t`, replaced by `(cl)`.
fn concluding_empty(steps: &str) -> String {
    let at = steps.rfind("(step t (cl").expect("the rule's step") + "(step t ".len();
    let mut depth = 0;
    let len = steps[at..]
        .char_indices()
        .find_map(|(i, c)| {
            depth += match c {
                '(' => 1,
                ')' => -1,
                _ => 0,
            };
            (depth == 0).then_some(i + 1)
        })
        .expect("a balanced conclusion");
    format!("{}(cl){}", &steps[..at], &steps[at + len..])
}

/// The satisfiable control, per mirrored rule, which the corpus's
/// assertions-dropped control cannot be for these certificates (their
/// refutation rests on `(assume e.a false)`, which is merely not a premise
/// once the assertions are dropped): the rule's own control steps, its step
/// concluding the empty clause, against the control's assertions alone. ay
/// answers `sat` for each such problem, every assumption is one of its
/// assertions, and so the walk could count the certificate as checked only
/// by accepting the rule's step: it must refuse (or not decide) exactly that
/// step, and with `CLEAN_PATH` the consumer must refuse the certificate.
#[test]
#[ntest::timeout(600_000)]
fn no_rule_refutes_its_satisfiable_control() {
    let mut failures = Vec::new();
    let mut solved = std::collections::BTreeSet::new();
    let mut replayed = 0;
    for control in CONTROLS {
        let mut problem = super::DECLARATIONS.to_string();
        for assertion in control.assertions {
            problem.push_str(&format!("(assert {assertion})\n"));
        }
        problem.push_str("(check-sat)\n");
        if solved.insert(control.assertions) {
            let (verdict, _) = super::one_shot(&problem, &[]);
            if verdict != "sat" {
                failures.push(format!("{}: ay answers {verdict:?}", control.rule));
            }
        }
        let proof = concluding_empty(control.steps);
        let coverage = mirror_certificate(&problem, &proof);
        if coverage.checked() || coverage.refutation.is_some() {
            failures.push(format!("{}: the empty clause is checked", control.rule));
        }
        let stray: Vec<&String> = coverage
            .refused
            .iter()
            .filter(|refusal| !refusal.starts_with("step t ("))
            .chain(
                coverage
                    .undetermined
                    .values()
                    .map(|(_, why)| why)
                    .filter(|why| !why.starts_with("step t:")),
            )
            .collect();
        if !stray.is_empty() {
            failures.push(format!("{}: not only step t: {stray:?}", control.rule));
        }
        let verdict = step_verdict(&problem, &proof, "t").unwrap_or_default();
        if verdict == "accepted" {
            failures.push(format!("{}: step t is accepted", control.rule));
        }
        if let Some(accepts) = clean_accepts(&problem, &proof) {
            replayed += 1;
            if accepts {
                failures.push(format!("{}: CLEAN_PATH accepts it", control.rule));
            }
        }
    }
    eprintln!(
        "satisfiable rule controls: {} rules, {} problems ay answers, \
         {replayed} replayed through CLEAN_PATH",
        CONTROLS.len(),
        solved.len()
    );
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
