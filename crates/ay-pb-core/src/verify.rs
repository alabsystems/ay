// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Independent verification of a solver's reported answer for an OPB instance.
//!
//! This is a *result* checker, not a *proof* checker. It answers two questions
//! about a solver run, using reasoning independent of the solver that produced
//! the answer:
//!
//! 1. **Is the reported model feasible, and does its objective match?** (always,
//!    pure Rust): every constraint is re-evaluated against the assignment on the
//!    `v` line, and the objective the assignment actually attains is compared to
//!    the value on the last `o` line.
//! 2. **Is a reported OPTIMUM really optimal?** (opt-in, via the external `z3`
//!    binary): we ask an *independent* SMT solver whether any feasible assignment
//!    beats the claimed optimum. If z3 proves none exists (`unsat`), the optimum
//!    is confirmed; if z3 finds a better one (`sat`), the solver's OPTIMUM was
//!    **wrong** — the single most dangerous error an optimizer can make.
//!
//! Why an *independent* checker: the solver has its own internal optimum
//! verification, but that shares the solver's codebase and so could share a bug
//! that produced a false answer. z3 is a separate implementation, so it catches
//! a false OPTIMUM without trusting any of the solver's reasoning. This is a
//! development / CI soundness gate, not a substitute for the certified-track
//! VeriPB proof pipeline (which formally checks the *derivation*). It is also
//! only useful on instances small enough for z3 to decide quickly.
//!
//! A SAT claim is fully verified by an independently checked feasible model. An
//! OPTIMUM claim additionally requires a matching objective and a confirmed z3
//! check. Missing, unknown, unsupported, unproved UNSAT, skipped, and
//! inconclusive claims remain explicitly unverified.

use std::io::Write;
use std::process::{Command, Stdio};

use crate::types::{PbConstraint, PbInstance, PbObjective, PbRel};

mod report;

pub use report::{UnverifiedReason, VerificationFailure, VerificationVerdict, VerifyReport};

/// Whether to run the independent z3 optimality cross-check.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Z3Mode {
    /// Never invoke z3 (model + objective checks only).
    Off,
    /// Invoke z3 if it is available on `PATH`.
    ///
    /// An unavailable or inconclusive checker leaves an optimum claim
    /// unverified; it never produces a fully verified report.
    Auto,
    /// Require z3 for an optimum claim.
    ///
    /// This compatibility mode has the same fail-closed verification verdict
    /// as [`Self::Auto`]: unavailable or inconclusive checks are unverified.
    Require,
}

/// The parsed `s` / `o` / `v` lines of a PB-competition-format solver output.
#[derive(Debug, Clone)]
pub struct SolverOutput {
    /// Status payload after `s ` (e.g. `OPTIMUM FOUND`, `SATISFIABLE`,
    /// `UNSATISFIABLE`, `UNKNOWN`). `None` if no `s` line was present.
    pub status: Option<String>,
    /// The last `o <value>` line (the best objective the solver reported).
    pub objective: Option<i128>,
    /// Assignment indexed by `var - 1` (true = variable set to 1), sized
    /// strictly to the declared header variable count. Out-of-range `v` tokens
    /// are ignored.
    pub assignment: Vec<bool>,
    /// Whether any `v` line was present at all.
    pub has_model: bool,
}

/// Outcome of the independent optimality cross-check.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OptimalityCheck {
    /// The status was not `OPTIMUM FOUND`, so optimality was not checked.
    NotApplicable,
    /// z3 was not run (mode `Off`, or `Auto` with z3 absent). Carries the reason.
    Skipped(String),
    /// z3 proved no feasible assignment beats the claimed optimum (`unsat`).
    Confirmed,
    /// z3 found a feasible assignment strictly better than the claimed optimum:
    /// the reported OPTIMUM is **wrong**. Carries a short detail string.
    Refuted(String),
    /// z3 returned `unknown` / timed out, so optimality is unconfirmed.
    Inconclusive(String),
}

/// Parse the `s` / `o` / `v` lines of a solver output.
///
/// `header_vars` fixes the assignment length so a fully-specified model has the
/// expected size even if the largest variable is left false on the `v` line.
/// Variable tokens outside `1..=header_vars` are ignored without allocating.
pub fn parse_solver_output(text: &str, header_vars: u32) -> SolverOutput {
    let mut status = None;
    let mut objective = None;
    let mut assignment: Vec<bool> = vec![false; header_vars as usize];
    let mut has_model = false;

    for line in text.lines() {
        let line = line.trim_end();
        if let Some(rest) = line.strip_prefix("s ") {
            status = Some(rest.trim().to_string());
        } else if let Some(rest) = line.strip_prefix("o ") {
            if let Ok(v) = rest.trim().parse::<i128>() {
                objective = Some(v); // keep the last one (best)
            }
        } else if line == "v" || line.starts_with("v ") {
            has_model = true;
            for tok in line[1..].split_whitespace() {
                let (val, name) = if let Some(rest) = tok.strip_prefix('-') {
                    (false, rest)
                } else {
                    (true, tok)
                };
                let digits = name.strip_prefix('x').unwrap_or(name);
                if let Ok(var) = digits.parse::<u32>() {
                    if var == 0 {
                        continue;
                    }
                    let Ok(idx) = usize::try_from(var - 1) else {
                        continue;
                    };
                    if idx >= assignment.len() {
                        continue;
                    }
                    assignment[idx] = val;
                }
            }
        }
    }

    SolverOutput {
        status,
        objective,
        assignment,
        has_model,
    }
}

/// Verify a solver output against an OPB instance.
///
/// `z3_timeout_secs` bounds each z3 query (soft `-T:` timeout).
pub fn verify(
    instance: &PbInstance,
    output: &SolverOutput,
    z3: Z3Mode,
    z3_timeout_secs: u64,
) -> VerifyReport {
    report::verify_with_checker(
        instance,
        output,
        z3,
        z3_timeout_secs,
        run_z3_optimality_check,
    )
}

/// Ask z3 whether any feasible assignment has objective <= `claimed - 1`.
/// `unsat` confirms `claimed` is optimal; `sat` refutes it.
fn run_z3_optimality_check(
    instance: &PbInstance,
    objective: &PbObjective,
    claimed: i128,
    timeout_secs: u64,
) -> OptimalityCheck {
    let Some(smt) = emit_smt2_better_than(instance, objective, claimed) else {
        return OptimalityCheck::Inconclusive(
            "claimed objective is i128::MIN; its strict improvement bound is outside the i128 verification range"
                .to_string(),
        );
    };
    match run_z3(&smt, timeout_secs) {
        Ok(Z3Result::Unsat) => OptimalityCheck::Confirmed,
        Ok(Z3Result::Sat) => OptimalityCheck::Refuted(format!(
            "z3 found a feasible assignment strictly better than the claimed optimum {claimed}"
        )),
        Ok(Z3Result::Unknown) => {
            OptimalityCheck::Inconclusive(format!("z3 returned unknown within {timeout_secs}s"))
        }
        Err(e) => match e {
            Z3Error::NotFound => OptimalityCheck::Skipped(
                "z3 not found on PATH (install z3 to enable this check)".to_string(),
            ),
            Z3Error::Io(msg) => {
                OptimalityCheck::Inconclusive(format!("z3 invocation failed: {msg}"))
            }
            Z3Error::UnsuccessfulExit(detail) => {
                OptimalityCheck::Inconclusive(format!("z3 did not exit successfully: {detail}"))
            }
        },
    }
}

enum Z3Result {
    Sat,
    Unsat,
    Unknown,
}

enum Z3Error {
    NotFound,
    Io(String),
    UnsuccessfulExit(String),
}

fn run_z3(smt2: &str, timeout_secs: u64) -> Result<Z3Result, Z3Error> {
    let mut child = Command::new("z3")
        .arg(format!("-T:{timeout_secs}"))
        .arg("-in")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .map_err(|e| {
            if e.kind() == std::io::ErrorKind::NotFound {
                Z3Error::NotFound
            } else {
                Z3Error::Io(e.to_string())
            }
        })?;

    if let Some(mut stdin) = child.stdin.take() {
        stdin
            .write_all(smt2.as_bytes())
            .map_err(|e| Z3Error::Io(e.to_string()))?;
    }
    let out = child
        .wait_with_output()
        .map_err(|e| Z3Error::Io(e.to_string()))?;
    if !out.status.success() {
        let detail = out.status.code().map_or_else(
            || "terminated by signal".to_string(),
            |code| format!("exit status {code}"),
        );
        return Err(Z3Error::UnsuccessfulExit(detail));
    }
    let stdout = String::from_utf8_lossy(&out.stdout);
    for line in stdout.lines() {
        match line.trim() {
            "unsat" => return Ok(Z3Result::Unsat),
            "sat" => return Ok(Z3Result::Sat),
            "unknown" => return Ok(Z3Result::Unknown),
            _ => {}
        }
    }
    Ok(Z3Result::Unknown)
}

/// Build an SMT-LIB2 query that is satisfiable iff some feasible assignment has
/// objective `<= claimed - 1`.
///
/// Variables are 0/1 **integers** (box-bounded `0 <= x <= 1`) and each term is
/// `coeff * product-of-literals` (`x` or `(- 1 x)` per literal). For linear
/// (single-literal) instances this is pure `QF_LIA` — z3 solves it directly with
/// its arithmetic engine, which is far faster than a Boolean + `ite` encoding
/// that forces case-splitting (the latter timed out on 1800-var instances).
/// Product terms (the NLC track) make it nonlinear, so the logic widens to
/// `ALL`.
fn emit_smt2_better_than(
    instance: &PbInstance,
    objective: &PbObjective,
    claimed: i128,
) -> Option<String> {
    let bound = claimed.checked_sub(1)?;
    // Collect referenced variables so we only declare what is used.
    let mut used: Vec<u32> = Vec::new();
    for c in &instance.constraints {
        for t in &c.terms {
            for l in &t.lits {
                used.push(l.var);
            }
        }
    }
    for t in &objective.terms {
        for l in &t.lits {
            used.push(l.var);
        }
    }
    used.sort_unstable();
    used.dedup();

    // Linear (all single-literal) => QF_LIA; any product term => nonlinear.
    let linear = instance
        .constraints
        .iter()
        .flat_map(|c| c.terms.iter())
        .chain(objective.terms.iter())
        .all(|t| t.lits.len() <= 1);

    let mut s = String::new();
    s.push_str(if linear {
        "(set-logic QF_LIA)\n"
    } else {
        "(set-logic ALL)\n"
    });
    for v in &used {
        s.push_str(&format!(
            "(declare-const x{v} Int)\n(assert (>= x{v} 0))\n(assert (<= x{v} 1))\n"
        ));
    }
    for c in &instance.constraints {
        s.push_str(&format!("(assert {})\n", constraint_smt(c)));
    }
    // objective <= claimed - 1
    s.push_str(&format!(
        "(assert (<= {} {}))\n",
        terms_sum_smt(&objective.terms),
        int_smt(bound)
    ));
    s.push_str("(check-sat)\n");
    Some(s)
}

fn constraint_smt(c: &PbConstraint) -> String {
    let lhs = terms_sum_smt(&c.terms);
    let rhs = int_smt(c.rhs);
    match c.rel {
        PbRel::Ge => format!("(>= {lhs} {rhs})"),
        PbRel::Eq => format!("(= {lhs} {rhs})"),
    }
}

fn terms_sum_smt(terms: &[crate::types::PbTerm]) -> String {
    if terms.is_empty() {
        return "0".to_string();
    }
    let parts: Vec<String> = terms.iter().map(term_smt).collect();
    if parts.len() == 1 {
        parts.into_iter().next().unwrap()
    } else {
        format!("(+ {})", parts.join(" "))
    }
}

fn term_smt(t: &crate::types::PbTerm) -> String {
    let coeff = int_smt(t.coeff);
    if t.lits.is_empty() {
        // empty product => constant term (coeff * 1)
        return coeff;
    }
    let factors: Vec<String> = t.lits.iter().map(lit_smt).collect();
    let product = if factors.len() == 1 {
        factors.into_iter().next().unwrap()
    } else {
        // product of 0/1 integers (nonlinear; NLC track only)
        format!("(* {})", factors.join(" "))
    };
    format!("(* {coeff} {product})")
}

/// A literal as a 0/1 integer expression: `x` (true) or `(- 1 x)` (negated).
fn lit_smt(l: &crate::types::PbLit) -> String {
    if l.negated {
        format!("(- 1 x{})", l.var)
    } else {
        format!("x{}", l.var)
    }
}

/// SMT-LIB2 integer literal (negatives are `(- n)`).
fn int_smt(v: i128) -> String {
    if v < 0 {
        format!("(- {})", v.unsigned_abs())
    } else {
        v.to_string()
    }
}

#[cfg(test)]
mod tests;
