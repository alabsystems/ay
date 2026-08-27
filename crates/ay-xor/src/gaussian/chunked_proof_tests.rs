// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Tests for Tseitin-chunked DRAT ladder emission (`chunked_proof`).

use super::*;
use crate::constraint::XorConstraint;
use crate::gaussian::GaussResult;

/// A chained system whose elimination accumulates a row of width
/// `width + 1` (far beyond `MAX_XOR_PROOF_ROW_VARS`) before unit rows
/// collapse it into a 0=1 conflict:
///   s_i ^ s_{i+1} ^ t_i = 0  (i in 0..width),  s_0 = 0,  s_width = 1,
///   t_i = 0.
fn wide_trace_constraints(width: usize) -> Vec<XorConstraint> {
    let s = |i: usize| i as VarId;
    let t = |i: usize| (width + 1 + i) as VarId;
    let mut constraints = Vec::new();
    for i in 0..width {
        constraints.push(XorConstraint::new(vec![s(i), s(i + 1), t(i)], false));
    }
    constraints.push(XorConstraint::new(vec![s(0)], false));
    constraints.push(XorConstraint::new(vec![s(width)], true));
    for i in 0..width {
        constraints.push(XorConstraint::new(vec![t(i)], false));
    }
    constraints
}

/// The exact input CNF the XOR groups above stand for: the full
/// truth-table encoding of every constraint.
fn constraints_to_cnf(constraints: &[XorConstraint]) -> (usize, Vec<Vec<i32>>) {
    let mut clauses = Vec::new();
    let mut max_var = 0usize;
    for c in constraints {
        let n = c.vars.len();
        for v in &c.vars {
            max_var = max_var.max(*v as usize + 1);
        }
        for assign in 0u32..(1 << n) {
            if (assign.count_ones() % 2 == 1) == c.rhs {
                continue; // right parity: not blocked
            }
            clauses.push(
                c.vars
                    .iter()
                    .enumerate()
                    .map(|(bit, &v)| {
                        let dimacs = v as i32 + 1;
                        if (assign >> bit) & 1 == 1 {
                            -dimacs
                        } else {
                            dimacs
                        }
                    })
                    .collect(),
            );
        }
    }
    (max_var, clauses)
}

fn script_to_drat(script: &[ExtProofStep]) -> String {
    let mut out = String::new();
    for step in script {
        let (prefix, clause) = match step {
            ExtProofStep::Add(c) => ("", c),
            ExtProofStep::Delete(c) => ("d ", c),
        };
        out.push_str(prefix);
        for lit in clause {
            out.push_str(&lit.to_dimacs().to_string());
            out.push(' ');
        }
        out.push_str("0\n");
    }
    out
}

/// The formerly-rejected wide-trace shape is accepted by the chunked
/// preflight, with a LINEAR (not exponential) addition count.
#[test]
fn test_chunked_plan_accepts_wide_trace_linearly() {
    let constraints = wide_trace_constraints(30);
    let mut solver = GaussianSolver::new(&constraints);
    assert!(matches!(solver.eliminate(), GaussResult::Conflict(_)));
    // Monolithic preflight rejects: the trace has steps wider than
    // MAX_XOR_PROOF_ROW_VARS.
    assert!(!solver.has_complete_proof_ladder());
    let state = solver
        .build_chunked_component_state()
        .expect("chunked plan must accept the wide trace");
    // The trace holds a few hundred steps of width <= 32. A monolithic
    // ladder would need 2^29+ clauses for a single wide step; the
    // chunked plan stays around a dozen clauses per step variable
    // (measured: 138,280 additions for this shape).
    assert!(
        state.total_additions() < 200_000,
        "chunked cost not linear: {}",
        state.total_additions()
    );
}

/// Rows wider than the rotation envelope among the ORIGINAL constraints
/// still reject (their input encoding cannot be chain-converted).
#[test]
fn test_chunked_plan_rejects_wide_original_rows() {
    let vars: Vec<VarId> = (0..=MAX_XOR_PROOF_ROW_VARS as VarId).collect();
    let constraints = vec![
        XorConstraint::new(vars.clone(), false),
        XorConstraint::new(vars, true),
    ];
    let mut solver = GaussianSolver::new(&constraints);
    assert!(matches!(solver.eliminate(), GaussResult::Conflict(_)));
    assert!(solver.build_chunked_component_state().is_none());
}

/// Narrow traces keep the monolithic path: the chunked state is never
/// consulted and the mono ladder output is unchanged.
#[test]
fn test_narrow_trace_prefers_monolithic_path() {
    let constraints = vec![
        XorConstraint::new(vec![0, 1, 2], false),
        XorConstraint::new(vec![1, 2, 3], false),
    ];
    let mut ext = crate::XorExtension::new(constraints);
    assert!(ext.has_complete_proof_ladders());
    ext.set_proof_fresh_var_base(4);
    assert!(ext.has_complete_proof_ladders());
    assert!(
        !ext.chunked_proof_active(),
        "mono envelope must stay monolithic"
    );
}

/// End-to-end: the chunked cone of the 0=1 conflict row — chain
/// definitions (RAT on fresh extension variables), rotation ladders for
/// original rows, position ladders for derived rows, deletions of
/// exhausted intermediates, and the final empty clause — is accepted by
/// dsr-trim against the exact input CNF. Skips when the checker binary
/// is not installed.
#[test]
fn test_chunked_wide_conflict_cone_verifies_with_dsr_trim() {
    let constraints = wide_trace_constraints(30);
    let (num_vars, cnf) = constraints_to_cnf(&constraints);
    let mut solver = GaussianSolver::new(&constraints);
    let GaussResult::Conflict(conflict_row) = solver.eliminate() else {
        panic!("wide trace must conflict at elimination");
    };
    let mut state = solver
        .build_chunked_component_state()
        .expect("chunked plan must accept the wide trace");
    let mut next_fresh = num_vars as VarId;
    let mut script = Vec::new();
    state.emit_row_cone(&solver, conflict_row, &mut next_fresh, &mut script);
    assert!(
        script
            .iter()
            .any(|s| matches!(s, ExtProofStep::Add(c) if c.is_empty())),
        "conflict cone must derive the empty clause"
    );
    assert!(
        script.iter().any(|s| matches!(s, ExtProofStep::Delete(_))),
        "exhausted intermediates must be deleted"
    );
    let additions = script
        .iter()
        .filter(|s| matches!(s, ExtProofStep::Add(_)))
        .count() as u64;
    assert!(additions <= state.total_additions());

    let Some(home) = std::env::var_os("HOME") else {
        return;
    };
    let checker = std::path::Path::new(&home).join("ay-bench/bin/dsr-trim");
    if !checker.exists() {
        eprintln!("SKIP dsr-trim validation: {} not found", checker.display());
        return;
    }
    let dir = std::env::temp_dir().join(format!(
        "ay_xor_chunked_test_{}_{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_nanos())
            .unwrap_or_default(),
    ));
    std::fs::create_dir_all(&dir).expect("create test dir");
    let cnf_path = dir.join("wide.cnf");
    let drat_path = dir.join("wide.drat");
    let mut cnf_text = format!("p cnf {} {}\n", num_vars, cnf.len());
    for clause in &cnf {
        for lit in clause {
            cnf_text.push_str(&lit.to_string());
            cnf_text.push(' ');
        }
        cnf_text.push_str("0\n");
    }
    std::fs::write(&cnf_path, cnf_text).expect("write cnf");
    std::fs::write(&drat_path, script_to_drat(&script)).expect("write drat");
    let output = std::process::Command::new(&checker)
        .arg(&cnf_path)
        .arg(&drat_path)
        .output()
        .expect("run dsr-trim");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        output.status.success() && stdout.contains("s VERIFIED UNSAT"),
        "dsr-trim rejected the chunked certificate (status {:?}):\n{}\n{}",
        output.status.code(),
        stdout,
        String::from_utf8_lossy(&output.stderr),
    );
    let _ = std::fs::remove_dir_all(&dir);
}
