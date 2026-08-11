// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Property-based soundness tests for QF_S string theory.
//!
//! Generates random QF_S formulas combining string operations (prefixof,
//! suffixof, contains, length constraints, concatenation equalities) and
//! cross-checks AY's result against Z3.
//!
//! Any disagreement on definite (sat/unsat) results is a soundness bug.
//! AY returning "unknown" when Z3 is definite is a completeness gap,
//! not a soundness issue.

use ay_dpll::Executor;
use ay_frontend::parse;
use proptest::prelude::*;
use std::process::Command;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::time::Duration;

/// Small alphabet for constant generation — keeps formulas tractable.
const ALPHABET: &[u8] = b"abcxyz";

/// Generate a random short string constant (1-4 chars from ALPHABET).
fn arb_string_constant() -> impl Strategy<Value = String> {
    proptest::collection::vec(proptest::sample::select(ALPHABET.to_vec()), 1..=4)
        .prop_map(|bytes| String::from_utf8(bytes).unwrap())
}

/// A string constraint that can appear in a QF_S formula.
#[derive(Clone, Debug)]
enum StringConstraint {
    /// str.prefixof(constant, variable)
    PrefixOf { constant: String, var: String },
    /// str.suffixof(constant, variable)
    SuffixOf { constant: String, var: String },
    /// str.contains(variable, constant)
    Contains { constant: String, var: String },
    /// (= variable (str.++ constant1 variable2))
    ConcatEqLeft {
        prefix: String,
        var_lhs: String,
        var_rhs: String,
    },
    /// (not (= variable1 variable2))
    Neq { var1: String, var2: String },
    /// (= (str.len variable) n)
    LenEq { var: String, len: usize },
    /// (>= (str.len variable) n)
    LenGe { var: String, len: usize },
}

impl StringConstraint {
    fn to_smt2(&self) -> String {
        match self {
            Self::PrefixOf { constant, var } => {
                format!("(assert (str.prefixof \"{constant}\" {var}))")
            }
            Self::SuffixOf { constant, var } => {
                format!("(assert (str.suffixof \"{constant}\" {var}))")
            }
            Self::Contains { constant, var } => {
                format!("(assert (str.contains {var} \"{constant}\"))")
            }
            Self::ConcatEqLeft {
                prefix,
                var_lhs,
                var_rhs,
            } => {
                format!("(assert (= {var_lhs} (str.++ \"{prefix}\" {var_rhs})))")
            }
            Self::Neq { var1, var2 } => {
                format!("(assert (not (= {var1} {var2})))")
            }
            Self::LenEq { var, len } => {
                format!("(assert (= (str.len {var}) {len}))")
            }
            Self::LenGe { var, len } => {
                format!("(assert (>= (str.len {var}) {len}))")
            }
        }
    }
}

/// Generate a random string constraint over variables x, y, z.
fn arb_constraint() -> impl Strategy<Value = StringConstraint> {
    let vars = vec!["x".to_string(), "y".to_string(), "z".to_string()];
    let var = proptest::sample::select(vars.clone());
    let var2 = proptest::sample::select(vars);

    prop_oneof![
        // PrefixOf with random constant
        (arb_string_constant(), var.clone()).prop_map(|(c, v)| StringConstraint::PrefixOf {
            constant: c,
            var: v
        }),
        // SuffixOf with random constant
        (arb_string_constant(), var.clone()).prop_map(|(c, v)| StringConstraint::SuffixOf {
            constant: c,
            var: v
        }),
        // Contains with random constant
        (arb_string_constant(), var.clone()).prop_map(|(c, v)| StringConstraint::Contains {
            constant: c,
            var: v
        }),
        // Concat equality
        (arb_string_constant(), var.clone(), var2.clone()).prop_map(|(p, v1, v2)| {
            StringConstraint::ConcatEqLeft {
                prefix: p,
                var_lhs: v1,
                var_rhs: v2,
            }
        }),
        // Disequality between two variables
        (var.clone(), var2).prop_map(|(v1, v2)| StringConstraint::Neq { var1: v1, var2: v2 }),
        // Length equality (small values)
        (var.clone(), 0usize..=8).prop_map(|(v, l)| StringConstraint::LenEq { var: v, len: l }),
        // Length lower bound
        (var, 1usize..=6).prop_map(|(v, l)| StringConstraint::LenGe { var: v, len: l }),
    ]
}

/// Generate a full QF_S formula with 2-5 constraints.
fn arb_qf_s_formula() -> impl Strategy<Value = String> {
    proptest::collection::vec(arb_constraint(), 2..=5).prop_map(|constraints| {
        let mut smt = String::new();
        smt.push_str("(set-logic QF_S)\n");
        smt.push_str("(declare-const x String)\n");
        smt.push_str("(declare-const y String)\n");
        smt.push_str("(declare-const z String)\n");
        for c in &constraints {
            smt.push_str(&c.to_smt2());
            smt.push('\n');
        }
        smt.push_str("(check-sat)\n");
        smt
    })
}

/// Generate a QF_SLIA formula (string + integer) with 2-5 constraints.
fn arb_qf_slia_formula() -> impl Strategy<Value = String> {
    proptest::collection::vec(arb_constraint(), 2..=5).prop_map(|constraints| {
        let mut smt = String::new();
        smt.push_str("(set-logic QF_SLIA)\n");
        smt.push_str("(declare-const x String)\n");
        smt.push_str("(declare-const y String)\n");
        smt.push_str("(declare-const z String)\n");
        for c in &constraints {
            smt.push_str(&c.to_smt2());
            smt.push('\n');
        }
        smt.push_str("(check-sat)\n");
        smt
    })
}

/// Run AY in-process with a timeout. Returns "sat", "unsat", "unknown", or "error".
fn run_ay_on_smt(smt: &str, timeout_secs: u64) -> String {
    let commands = match parse(smt) {
        Ok(c) => c,
        Err(_) => return "error".to_string(),
    };

    let mut executor = Executor::new();
    let interrupt = Arc::new(AtomicBool::new(false));
    executor.set_interrupt(Arc::clone(&interrupt));

    let (cancel_tx, cancel_rx) = std::sync::mpsc::channel();
    let timer_interrupt = Arc::clone(&interrupt);
    let timer = std::thread::spawn(move || {
        if cancel_rx
            .recv_timeout(Duration::from_secs(timeout_secs))
            .is_err()
        {
            timer_interrupt.store(true, Ordering::Relaxed);
        }
    });

    let results = executor.execute_all(&commands);
    let timed_out = interrupt.load(Ordering::Relaxed);
    let _ = cancel_tx.send(());
    let _ = timer.join();

    if timed_out {
        return "unknown".to_string();
    }

    match results {
        Ok(results) => {
            for r in results {
                let lower = r.to_lowercase();
                if lower == "sat" || lower == "unsat" || lower == "unknown" {
                    return lower;
                }
            }
            "unknown".to_string()
        }
        Err(_) => "error".to_string(),
    }
}

/// Run Z3 on an SMT-LIB string with a timeout. Returns "sat", "unsat", "unknown", or "error".
fn run_z3_on_smt(smt: &str, timeout_secs: u64) -> String {
    let mut child = match Command::new("z3")
        .arg(format!("-T:{timeout_secs}"))
        .arg("-in")
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
    {
        Ok(c) => c,
        Err(_) => return "error".to_string(),
    };

    if let Some(mut stdin) = child.stdin.take() {
        use std::io::Write;
        let _ = stdin.write_all(smt.as_bytes());
    }

    let output = match child.wait_with_output() {
        Ok(o) => o,
        Err(_) => return "error".to_string(),
    };

    let stdout = String::from_utf8_lossy(&output.stdout);
    for line in stdout.lines() {
        let line = line.trim().to_lowercase();
        if line == "sat" || line == "unsat" || line == "unknown" {
            return line;
        }
    }
    "unknown".to_string()
}

fn z3_available() -> bool {
    Command::new("z3")
        .arg("--version")
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false)
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(200))]

    /// Property: AY must never return a definite result that contradicts Z3.
    ///
    /// If Z3 says SAT and AY says UNSAT (or vice versa), that is a soundness bug.
    /// AY returning "unknown" is always acceptable (completeness gap, not soundness).
    #[test]
    fn qf_s_soundness_vs_z3(formula in arb_qf_s_formula()) {
        if !z3_available() {
            return Ok(());
        }

        let ay_result = run_ay_on_smt(&formula, 5);
        let z3_result = run_z3_on_smt(&formula, 5);

        // Only check when both are definite
        if (ay_result == "sat" || ay_result == "unsat")
            && (z3_result == "sat" || z3_result == "unsat")
        {
            prop_assert_eq!(
                &ay_result,
                &z3_result,
                "SOUNDNESS BUG: AY={}, Z3={} on formula:\n{}",
                ay_result,
                z3_result,
                formula
            );
        }
    }

    /// Property: AY must never return a definite result that contradicts Z3
    /// on QF_SLIA formulas (strings + integer length constraints).
    #[test]
    fn qf_slia_soundness_vs_z3(formula in arb_qf_slia_formula()) {
        if !z3_available() {
            return Ok(());
        }

        let ay_result = run_ay_on_smt(&formula, 5);
        let z3_result = run_z3_on_smt(&formula, 5);

        if (ay_result == "sat" || ay_result == "unsat")
            && (z3_result == "sat" || z3_result == "unsat")
        {
            prop_assert_eq!(
                &ay_result,
                &z3_result,
                "SOUNDNESS BUG: AY={}, Z3={} on formula:\n{}",
                ay_result,
                z3_result,
                formula
            );
        }
    }
}

// Targeted proptest for prefix/suffix conflict detection (#6326 regression).
//
// Generates formulas with multiple prefixof/suffixof constraints on the same
// variable with conflicting constants. AY must never return SAT on these.
proptest! {
    #![proptest_config(ProptestConfig::with_cases(100))]

    #[test]
    fn prefix_conflict_never_sat(
        c1 in arb_string_constant(),
        c2 in arb_string_constant(),
    ) {
        // Only test when constants conflict at some position
        if c1.is_empty() || c2.is_empty() {
            return Ok(());
        }
        let min_len = c1.len().min(c2.len());
        let prefix_conflict = c1[..min_len] != c2[..min_len];
        if !prefix_conflict {
            return Ok(());
        }

        let formula = format!(
            "(set-logic QF_S)\n\
             (declare-const x String)\n\
             (assert (str.prefixof \"{c1}\" x))\n\
             (assert (str.prefixof \"{c2}\" x))\n\
             (check-sat)\n"
        );

        let ay_result = run_ay_on_smt(&formula, 5);
        prop_assert_ne!(
            ay_result,
            "sat",
            "SOUNDNESS BUG: prefixof(\"{}\",x) AND prefixof(\"{}\",x) returned SAT",
            c1, c2
        );
    }

    #[test]
    fn suffix_conflict_never_sat(
        c1 in arb_string_constant(),
        c2 in arb_string_constant(),
    ) {
        if c1.is_empty() || c2.is_empty() {
            return Ok(());
        }
        // Check suffix conflict: last min_len chars differ
        let min_len = c1.len().min(c2.len());
        let suffix1 = &c1[c1.len() - min_len..];
        let suffix2 = &c2[c2.len() - min_len..];
        if suffix1 == suffix2 {
            return Ok(());
        }

        let formula = format!(
            "(set-logic QF_S)\n\
             (declare-const x String)\n\
             (assert (str.suffixof \"{c1}\" x))\n\
             (assert (str.suffixof \"{c2}\" x))\n\
             (check-sat)\n"
        );

        let ay_result = run_ay_on_smt(&formula, 5);
        prop_assert_ne!(
            ay_result,
            "sat",
            "SOUNDNESS BUG: suffixof(\"{}\",x) AND suffixof(\"{}\",x) returned SAT",
            c1, c2
        );
    }
}
