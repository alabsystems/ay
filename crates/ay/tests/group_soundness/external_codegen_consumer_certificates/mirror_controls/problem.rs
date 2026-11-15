// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The problem a certificate refutes is read from the problem alone, at the
//! scope live at its query, and a proof may not (re)define a symbol the
//! problem uses.
//!
//! REGRESSION (measured 2026-10-07 on 4373bc24b): every refused case below
//! refutes a satisfiable problem and was counted as checked step by step.
//! The mirror expanded the proof's `define-fun` macros inside the problem's
//! assertions (`macro_shadow`, `false_macro`), and took every `assert` of the
//! script as a premise, retracted (`push_pop`, `reset_assertions`, `reset`)
//! or after the query (`after_check_sat`).
//!
//! The consumer: Clean 7330fa6c (the `clean 0.9.0` Trust's stage2 tools
//! carry) refuses both macro cases at `assume a0` ("assumption not present
//! in the problem"), but PASSES `push_pop`, `reset_assertions` and
//! `after_check_sat` as fully verified (measured 2026-10-07): its vendored
//! Carcara's `parse_problem` ignored `push`, `pop`, `reset` and
//! `reset-assertions` and read assertions after a `check-sat`. Clean
//! 4993e9d5c (fixes 36, 37: `check_script_command` in
//! `third-party/carcara/carcara/src/parser/mod.rs`) refuses those scripts at
//! parse; the Clean Trust pins predates it. With `CLEAN_PATH` the consumer's
//! verdict on those three is printed, and only the macro cases must agree.

use super::super::consumer_rules::{mirror_certificate, step_verdict};
use super::clean_accepts;

const REFUTE_FALSE: &str = "(assume a0 false)\n(step t1 (cl (not false)) :rule false)\n\
     (step t2 (cl) :rule resolution :premises (a0 t1))\n";

/// `(name, problem body, proof prefix, why the mirror must not check it)`,
/// each refuting `false` after the prefix. Every problem is satisfiable.
const REFUSED: &[(&str, &str, &str, &str)] = &[
    (
        "macro_shadow",
        "(assert p)\n(check-sat)\n",
        "(define-fun p () Bool false)\n",
        "macro",
    ),
    (
        "false_macro",
        "(assert p)\n(check-sat)\n",
        "(define-fun p () Bool false)\n",
        "macro",
    ),
    (
        "push_pop",
        "(push 1)\n(assert false)\n(pop 1)\n(assert p)\n(check-sat)\n",
        "",
        "script",
    ),
    (
        "nested_pop",
        "(push 1)\n(assert p)\n(push 2)\n(assert false)\n(pop 2)\n(check-sat)\n",
        "",
        "script",
    ),
    (
        "reset_assertions",
        "(assert false)\n(reset-assertions)\n(assert p)\n(check-sat)\n",
        "",
        "script",
    ),
    (
        "reset",
        "(assert false)\n(reset)\n(declare-const p Bool)\n(assert p)\n(check-sat)\n",
        "",
        "script",
    ),
    (
        "after_check_sat",
        "(assert p)\n(check-sat)\n(assert false)\n",
        "",
        "script",
    ),
    (
        "pop_below_bottom",
        "(assert false)\n(pop 1)\n(assert p)\n(check-sat)\n",
        "",
        "script",
    ),
];

/// The same shapes where the refuted assertion is live at the query, and a
/// proof macro whose name the problem does not use.
const ACCEPTED: &[(&str, &str, &str)] = &[
    ("live_push", "(push 1)\n(assert false)\n(check-sat)\n", ""),
    (
        "popped_other",
        "(push 1)\n(assert p)\n(pop 1)\n(assert false)\n(check-sat)\n",
        "",
    ),
    (
        "check_sat_assuming",
        "(assert p)\n(check-sat-assuming (false))\n",
        "",
    ),
    (
        "fresh_macro",
        "(assert false)\n(check-sat)\n",
        "(define-fun f () Bool false)\n",
    ),
];

fn problem(body: &str) -> String {
    format!("(set-logic ALL)\n(declare-const p Bool)\n{body}")
}

fn proof(name: &str, prefix: &str) -> String {
    let refutation = if name == "macro_shadow" {
        REFUTE_FALSE.replacen("a0 false", "a0 p", 1)
    } else if name == "fresh_macro" {
        REFUTE_FALSE.replacen("a0 false", "a0 f", 1)
    } else {
        REFUTE_FALSE.to_string()
    };
    format!("{prefix}{refutation}")
}

#[test]
fn a_certificate_refutes_only_the_problem_live_at_its_query() {
    let mut failures = Vec::new();
    for &(name, body, prefix, kind) in REFUSED {
        let (problem, proof) = (problem(body), proof(name, prefix));
        let coverage = mirror_certificate(&problem, &proof);
        if coverage.checked() {
            failures.push(format!("{name}: checked"));
        }
        let a0 = step_verdict(&problem, &proof, "a0").unwrap_or_default();
        let redefined = coverage
            .refused
            .iter()
            .any(|refusal| refusal.contains("defines p, a symbol the problem uses"));
        if kind == "macro" && !redefined {
            failures.push(format!("{name}: the redefinition is not refused"));
        }
        if a0 == "accepted" && name != "pop_below_bottom" {
            failures.push(format!("{name}: assume a0 is accepted"));
        }
        match clean_accepts(&problem, &proof) {
            Some(true) if kind == "macro" => {
                failures.push(format!("{name}: CLEAN_PATH accepts it"));
            }
            Some(accepts) => eprintln!("{name}: CLEAN_PATH accepts it: {accepts}"),
            None => {}
        }
    }
    for &(name, body, prefix) in ACCEPTED {
        let (problem, proof) = (problem(body), proof(name, prefix));
        let coverage = mirror_certificate(&problem, &proof);
        if !coverage.checked() {
            failures.push(format!(
                "{name}: not checked: {:?} {:?}",
                coverage.refused, coverage.undetermined
            ));
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
