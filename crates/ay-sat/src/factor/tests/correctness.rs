// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Factorization structural and satisfiability correctness regressions.

use super::*;

/// Validate structural invariants of a FactorApplication against the CaDiCaL
/// proof transaction pattern and the flattened FactorResult.
fn validate_application(app: &FactorApplication, result: &FactorResult) {
    let fresh_pos = Literal::positive(app.fresh_var);
    let fresh_neg = Literal::negative(app.fresh_var);

    // Each divider is (fresh ∨ factor_j).
    for (i, div) in app.divider_clauses.iter().enumerate() {
        assert_eq!(div.len(), 2, "dividers are binary");
        assert_eq!(div[0], fresh_pos, "divider[0] = fresh");
        assert_eq!(div[1], app.factors[i], "divider[1] = factor_i");
    }
    // Each quotient has ¬fresh as first literal.
    for qc in &app.quotient_clauses {
        assert!(qc.len() >= 2, "quotient clause non-trivial");
        assert_eq!(qc[0], fresh_neg, "quotient[0] = ¬fresh");
    }
    // Blocked clause: (¬fresh ∨ ¬f_1 ∨ ¬f_2 ∨ ...).
    assert_eq!(app.blocked_clause.len(), 1 + app.factors.len());
    assert_eq!(app.blocked_clause[0], fresh_neg, "blocked[0] = ¬fresh");
    for (i, &f) in app.factors.iter().enumerate() {
        assert_eq!(app.blocked_clause[i + 1], f.negated());
    }
    // Completeness: deletes = factors × quotients.
    assert_eq!(
        app.to_delete.len(),
        app.factors.len() * app.quotient_clauses.len()
    );
    // Flattened consistency.
    for div in &app.divider_clauses {
        assert!(
            result.new_clauses.contains(div),
            "divider missing from result"
        );
    }
    for qc in &app.quotient_clauses {
        assert!(
            result.new_clauses.contains(qc),
            "quotient missing from result"
        );
    }
}

#[test]
fn test_factor_application_proof_structure() {
    // Verify FactorApplication proof invariants on a 2×3 ternary matrix.
    let mut clause_db = ClauseArena::new();
    let a = lit(0, true);
    let b = lit(1, true);
    let c = lit(2, true);
    let d = lit(3, true);
    let e = lit(4, true);
    for lits in [
        [a, c, d],
        [b, c, d],
        [a, c, e],
        [b, c, e],
        [a, d, e],
        [b, d, e],
    ] {
        clause_db.add(&lits, false);
    }
    let mut occ = OccList::new(6);
    for ci in clause_db.indices() {
        occ.add_clause(ci, clause_db.literals(ci));
    }
    let result = Factor::new(6).run(
        &clause_db,
        &occ,
        &[0i8; 12],
        &[crate::solver::lifecycle::VarState::Active; 6],
        &FactorConfig {
            next_var_id: 6,
            effort_limit: u64::MAX,
            elim_bound: 0,
        },
    );
    if result.factored_count == 0 {
        return;
    }
    assert_eq!(
        result.applications.len() + result.self_subsuming.len(),
        result.factored_count
    );
    for app in &result.applications {
        validate_application(app, &result);
    }
}

fn sat_status(clauses: &[Vec<Literal>], num_vars: usize) -> bool {
    if num_vars >= usize::BITS as usize {
        return false;
    }
    let total = 1usize << num_vars;
    (0..total).any(|mask| {
        clauses.iter().all(|clause| {
            clause.iter().any(|lit| {
                let var = lit.variable().index();
                if var >= num_vars {
                    return false;
                }
                let val = ((mask >> var) & 1) == 1;
                (lit.is_positive() && val) || (!lit.is_positive() && !val)
            })
        })
    })
}

#[test]
fn test_factor_preserves_satisfiability_small_random() {
    // Search small formulas for a SAT/UNSAT flip after one factor.run pass.
    // This catches unsound matrix extraction in the clean-room port.
    let mut seed: u64 = 0xC0FFEE;
    let mut next_u32 = || {
        seed ^= seed << 7;
        seed ^= seed >> 9;
        seed ^= seed << 8;
        seed as u32
    };

    for _case in 0..200 {
        let num_vars = 5usize;
        let mut clause_db = ClauseArena::new();
        let mut original: Vec<Vec<Literal>> = Vec::new();

        let clause_count = 6 + (next_u32() as usize % 6);
        for _ in 0..clause_count {
            let mut clause: Vec<Literal> = Vec::new();
            while clause.len() < 3 {
                let v = (next_u32() as usize % num_vars) as u32;
                let pos = (next_u32() & 1) == 0;
                let lit = lit(v, pos);
                if clause.iter().any(|&x| x == lit || x == lit.negated()) {
                    continue;
                }
                clause.push(lit);
            }
            clause_db.add(&clause, false);
            original.push(clause);
        }

        let mut occ = OccList::new(num_vars);
        for ci in clause_db.indices() {
            let lits = clause_db.literals(ci);
            occ.add_clause(ci, lits);
        }

        let vals = vec![0i8; num_vars * 2]; // all unassigned
        let var_states = vec![crate::solver::lifecycle::VarState::Active; num_vars];
        let mut factor = Factor::new(num_vars);
        let result = factor.run(
            &clause_db,
            &occ,
            &vals,
            &var_states,
            &FactorConfig {
                next_var_id: num_vars,
                effort_limit: u64::MAX,
                elim_bound: 0,
            },
        );
        assert_eq!(
            result.applications.len() + result.self_subsuming.len(),
            result.factored_count
        );
        if result.factored_count == 0 {
            continue;
        }

        let mut transformed: Vec<Vec<Literal>> = Vec::new();
        for ci in clause_db.indices() {
            if result.to_delete.contains(&ci) {
                continue;
            }
            if clause_db.is_empty_clause(ci) || clause_db.is_learned(ci) {
                continue;
            }
            transformed.push(clause_db.literals(ci).to_vec());
        }
        transformed.extend(result.new_clauses.clone());

        let mut max_var = 0usize;
        for clause in &transformed {
            for &l in clause {
                max_var = max_var.max(l.variable().index());
            }
        }
        let transformed_vars = max_var + 1;

        let orig_sat = sat_status(&original, num_vars);
        let new_sat = sat_status(&transformed, transformed_vars);
        assert_eq!(
            orig_sat, new_sat,
            "factor SAT flip detected: orig_sat={orig_sat} new_sat={new_sat} deleted={} added={} factored={}",
            result.to_delete.len(),
            result.new_clauses.len(),
            result.factored_count
        );
    }
}
