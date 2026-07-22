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

use std::io::Write;
use std::process::{Command, Stdio};

use crate::solver::{eval_constraint, eval_objective};
use crate::types::{PbConstraint, PbInstance, PbObjective, PbRel};

/// Whether to run the independent z3 optimality cross-check.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Z3Mode {
    /// Never invoke z3 (model + objective checks only).
    Off,
    /// Invoke z3 if it is available on `PATH`; skip (do not fail) otherwise.
    Auto,
    /// Require z3: if it is unavailable or inconclusive, that is reported (and
    /// makes the overall result not fully verified).
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
    /// Assignment indexed by `var - 1` (true = variable set to 1). Sized to the
    /// largest variable mentioned on the `v` lines or the header, whichever is
    /// larger.
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

/// Full verification report. `ok` is the overall pass/fail used for exit codes.
#[derive(Debug, Clone)]
pub struct VerifyReport {
    pub status: Option<String>,
    /// True if the output carried a model that could be checked.
    pub checked_model: bool,
    pub total_constraints: usize,
    pub violated_constraints: usize,
    pub claimed_objective: Option<i128>,
    pub computed_objective: Option<i128>,
    /// `Some(true/false)` when both a claimed and computed objective exist.
    pub objective_matches: Option<bool>,
    pub optimality: OptimalityCheck,
    /// Overall verdict: model feasible, objective consistent, and optimality not
    /// refuted (and, under `Z3Mode::Require`, actually confirmed for OPTIMUM).
    pub ok: bool,
    /// Human-readable findings, in order.
    pub messages: Vec<String>,
}

/// Parse the `s` / `o` / `v` lines of a solver output.
///
/// `header_vars` seeds the assignment length so a fully-specified model has the
/// expected size even if the largest variable is left false on the `v` line.
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
                    let idx = (var - 1) as usize;
                    if idx >= assignment.len() {
                        assignment.resize(idx + 1, false);
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

fn status_is_optimum(status: &Option<String>) -> bool {
    status
        .as_deref()
        .map(|s| s.eq_ignore_ascii_case("OPTIMUM FOUND"))
        .unwrap_or(false)
}

fn status_is_model_bearing(status: &Option<String>) -> bool {
    status
        .as_deref()
        .map(|s| s.eq_ignore_ascii_case("OPTIMUM FOUND") || s.eq_ignore_ascii_case("SATISFIABLE"))
        .unwrap_or(false)
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
    let mut messages = Vec::new();
    let mut ok = true;

    let total_constraints = instance.constraints.len();
    let mut violated_constraints = 0;
    let mut checked_model = false;
    let mut computed_objective = None;
    let mut objective_matches = None;

    if status_is_model_bearing(&output.status) {
        if !output.has_model {
            messages.push("status claims a model but no `v` line was present".to_string());
            ok = false;
        } else {
            checked_model = true;
            violated_constraints = instance
                .constraints
                .iter()
                .filter(|c| !eval_constraint(c, &output.assignment))
                .count();
            if violated_constraints == 0 {
                messages.push(format!(
                    "model feasible: {total_constraints}/{total_constraints} constraints satisfied"
                ));
            } else {
                messages.push(format!(
                    "MODEL INFEASIBLE: {violated_constraints}/{total_constraints} constraints violated"
                ));
                ok = false;
            }

            if let Some(obj) = instance.objective.as_ref() {
                let computed = eval_objective(obj, &output.assignment);
                computed_objective = Some(computed);
                if let Some(claimed) = output.objective {
                    let matches = computed == claimed;
                    objective_matches = Some(matches);
                    if matches {
                        messages.push(format!(
                            "objective consistent: claimed = computed = {claimed}"
                        ));
                    } else {
                        messages.push(format!(
                            "OBJECTIVE MISMATCH: claimed o {claimed}, model attains {computed}"
                        ));
                        ok = false;
                    }
                } else {
                    messages.push(format!(
                        "objective not reported on an `o` line; model attains {computed}"
                    ));
                }
            }
        }
    } else if output.status.as_deref() == Some("UNSATISFIABLE")
        || output
            .status
            .as_deref()
            .map(|s| s.eq_ignore_ascii_case("UNSATISFIABLE"))
            .unwrap_or(false)
    {
        messages.push("status UNSATISFIABLE (no model to check)".to_string());
    } else {
        messages.push(format!(
            "status {:?}: nothing to model-check",
            output.status.as_deref().unwrap_or("<none>")
        ));
    }

    // Independent optimality cross-check (only meaningful for OPTIMUM with a
    // claimed objective and a feasible model already confirmed above).
    let optimality = if !status_is_optimum(&output.status) {
        OptimalityCheck::NotApplicable
    } else if z3 == Z3Mode::Off {
        OptimalityCheck::Skipped("z3 check disabled (--no-z3)".to_string())
    } else if violated_constraints > 0 {
        OptimalityCheck::Skipped("model infeasible; optimality moot".to_string())
    } else {
        match output.objective {
            None => OptimalityCheck::Skipped("no claimed objective".to_string()),
            Some(claimed) => match instance.objective.as_ref() {
                None => OptimalityCheck::Skipped("instance has no objective".to_string()),
                Some(obj) => run_z3_optimality_check(instance, obj, claimed, z3_timeout_secs),
            },
        }
    };

    match &optimality {
        OptimalityCheck::Confirmed => messages.push(format!(
            "independent optimality (z3): no feasible solution beats {} \u{2192} OPTIMUM CONFIRMED",
            output.objective.unwrap_or_default()
        )),
        OptimalityCheck::Refuted(detail) => {
            messages.push(format!("UNSOUND OPTIMUM (z3): {detail}"));
            ok = false;
        }
        OptimalityCheck::Inconclusive(detail) => {
            messages.push(format!("optimality unconfirmed (z3): {detail}"));
            if z3 == Z3Mode::Require {
                ok = false;
            }
        }
        OptimalityCheck::Skipped(detail) => {
            messages.push(format!("optimality not checked: {detail}"));
            if z3 == Z3Mode::Require && status_is_optimum(&output.status) {
                ok = false;
            }
        }
        OptimalityCheck::NotApplicable => {}
    }

    VerifyReport {
        status: output.status.clone(),
        checked_model,
        total_constraints,
        violated_constraints,
        claimed_objective: output.objective,
        computed_objective,
        objective_matches,
        optimality,
        ok,
        messages,
    }
}

/// Ask z3 whether any feasible assignment has objective <= `claimed - 1`.
/// `unsat` confirms `claimed` is optimal; `sat` refutes it.
fn run_z3_optimality_check(
    instance: &PbInstance,
    objective: &PbObjective,
    claimed: i128,
    timeout_secs: u64,
) -> OptimalityCheck {
    let smt = emit_smt2_better_than(instance, objective, claimed);
    match run_z3(&smt, timeout_secs) {
        Ok(Z3Result::Unsat) => OptimalityCheck::Confirmed,
        Ok(Z3Result::Sat) => OptimalityCheck::Refuted(format!(
            "z3 found a feasible assignment with objective <= {} (better than the claimed optimum {claimed})",
            claimed - 1
        )),
        Ok(Z3Result::Unknown) => {
            OptimalityCheck::Inconclusive(format!("z3 returned unknown within {timeout_secs}s"))
        }
        Err(e) => match e {
            Z3Error::NotFound => OptimalityCheck::Skipped(
                "z3 not found on PATH (install z3 to enable this check)".to_string(),
            ),
            Z3Error::Io(msg) => OptimalityCheck::Inconclusive(format!("z3 invocation failed: {msg}")),
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
fn emit_smt2_better_than(instance: &PbInstance, objective: &PbObjective, claimed: i128) -> String {
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
    let bound = claimed - 1;
    s.push_str(&format!(
        "(assert (<= {} {}))\n",
        terms_sum_smt(&objective.terms),
        int_smt(bound)
    ));
    s.push_str("(check-sat)\n");
    s
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
mod tests {
    use super::*;
    use crate::types::{PbLit, PbTerm};

    fn lit(var: u32) -> PbLit {
        PbLit {
            var,
            negated: false,
        }
    }
    fn term(coeff: i128, var: u32) -> PbTerm {
        PbTerm {
            coeff,
            lits: vec![lit(var)],
        }
    }
    fn ge(terms: Vec<PbTerm>, rhs: i128) -> PbConstraint {
        PbConstraint {
            terms,
            rel: PbRel::Ge,
            rhs,
        }
    }

    fn instance() -> PbInstance {
        // min x1 + x2 + x3  s.t.  x1 + x2 + x3 >= 2   (optimum = 2)
        PbInstance {
            num_vars: 3,
            num_constraints: 1,
            constraints: vec![ge(vec![term(1, 1), term(1, 2), term(1, 3)], 2)],
            objective: Some(PbObjective {
                terms: vec![term(1, 1), term(1, 2), term(1, 3)],
            }),
        }
    }

    #[test]
    fn parses_multi_vline_and_objective() {
        let out = "c hi\no 5\no 2\ns OPTIMUM FOUND\nv x1 -x2\nv x3\n";
        let p = parse_solver_output(out, 3);
        assert_eq!(p.status.as_deref(), Some("OPTIMUM FOUND"));
        assert_eq!(p.objective, Some(2));
        assert!(p.has_model);
        assert_eq!(p.assignment, vec![true, false, true]);
    }

    #[test]
    fn feasible_model_with_matching_objective_passes_without_z3() {
        let inst = instance();
        // x1=1,x2=1,x3=0 -> feasible, objective 2
        let out = parse_solver_output("o 2\ns OPTIMUM FOUND\nv x1 x2 -x3\n", 3);
        let r = verify(&inst, &out, Z3Mode::Off, 10);
        assert_eq!(r.violated_constraints, 0);
        assert_eq!(r.computed_objective, Some(2));
        assert_eq!(r.objective_matches, Some(true));
        assert!(r.ok, "should pass model+objective checks: {:?}", r.messages);
        assert_eq!(
            r.optimality,
            OptimalityCheck::Skipped("z3 check disabled (--no-z3)".to_string())
        );
    }

    #[test]
    fn infeasible_model_fails() {
        let inst = instance();
        // x1=1,x2=0,x3=0 -> sum 1 < 2, infeasible
        let out = parse_solver_output("o 1\ns SATISFIABLE\nv x1 -x2 -x3\n", 3);
        let r = verify(&inst, &out, Z3Mode::Off, 10);
        assert_eq!(r.violated_constraints, 1);
        assert!(!r.ok);
    }

    #[test]
    fn objective_mismatch_fails() {
        let inst = instance();
        // model attains 2 but claims 1
        let out = parse_solver_output("o 1\ns OPTIMUM FOUND\nv x1 x2 -x3\n", 3);
        let r = verify(&inst, &out, Z3Mode::Off, 10);
        assert_eq!(r.objective_matches, Some(false));
        assert!(!r.ok);
    }

    #[test]
    fn smt2_encodes_constraint_and_bound() {
        let inst = instance();
        let smt = emit_smt2_better_than(&inst, inst.objective.as_ref().unwrap(), 2);
        // 0/1 integer encoding (box-bounded), not Bool+ite.
        assert!(smt.contains("(declare-const x1 Int)"));
        assert!(smt.contains("(assert (<= x1 1))"));
        assert!(smt.contains("(set-logic QF_LIA)"));
        assert!(smt.contains("(>= (+ "));
        // objective <= claimed-1 = 1
        assert!(smt.contains("(<= (+ "));
        assert!(smt.contains("(check-sat)"));
    }

    #[test]
    fn int_smt_handles_negatives() {
        assert_eq!(int_smt(5), "5");
        assert_eq!(int_smt(-5), "(- 5)");
        assert_eq!(int_smt(0), "0");
    }
}
