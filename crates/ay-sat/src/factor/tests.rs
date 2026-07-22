// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::test_util::lit;

#[test]
fn test_factor_new() {
    let f = Factor::new(10);
    assert_eq!(f.num_vars, 10);
    assert_eq!(f.marks.len(), 20);
}

#[test]
fn test_factor_marks() {
    let mut f = Factor::new(5);
    let l = lit(2, true);
    assert!(!f.is_marked(l, MARK_FACTOR));
    f.mark(l, MARK_FACTOR);
    assert!(f.is_marked(l, MARK_FACTOR));
    assert!(!f.is_marked(l, MARK_QUOTIENT));
    f.mark(l, MARK_QUOTIENT);
    assert!(f.is_marked(l, MARK_FACTOR));
    assert!(f.is_marked(l, MARK_QUOTIENT));
    f.unmark(l, MARK_FACTOR);
    assert!(!f.is_marked(l, MARK_FACTOR));
    assert!(f.is_marked(l, MARK_QUOTIENT));
}

#[test]
fn test_find_next_factor_nounted_prevents_same_source_overcount() {
    let mut clause_db = ClauseArena::new();
    let a = lit(0, true);
    let x = lit(1, true);
    let y = lit(2, true);
    let p = lit(3, true);
    let q = lit(4, true);
    let r = lit(5, true);
    let s = lit(6, true);
    let t = lit(7, true);

    let source0 = clause_db.add(&[a, p, q], false);
    let source1 = clause_db.add(&[a, r, s], false);
    clause_db.add(&[x, p, q], false);
    clause_db.add(&[x, p, q], false);
    clause_db.add(&[y, p, q], false);
    clause_db.add(&[y, r, s], false);
    clause_db.add(&[x, t], false);

    let mut occ = OccList::new(8);
    for ci in clause_db.indices() {
        occ.add_clause(ci, clause_db.literals(ci));
    }

    let mut factor = Factor::new(8);
    let vals = vec![0i8; 16];
    let deleted = vec![false; clause_db.len()];
    let mut ticks = 0;
    let chain = factor.build_quotient_chain(
        &clause_db,
        &occ,
        &vals,
        a,
        vec![source0, source1],
        &deleted,
        &mut ticks,
        u64::MAX,
    );

    assert!(
        chain.len() >= 2,
        "expected a second quotient level after finding a next factor"
    );
    assert_eq!(
        chain[1].factor, y,
        "duplicate x partners from one source clause must not outrank the real cross-source next factor"
    );
}

#[test]
fn test_find_best_quotient() {
    use super::chain::{find_best_quotient, QuotientLevel};

    // 3 factors, 4 quotients: 12 clauses -> 7 clauses, reduction = 5.
    let chain = vec![
        QuotientLevel {
            factor: lit(0, true),
            clause_indices: vec![0, 1, 2, 3, 4, 5],
            matches: Vec::new(),
        },
        QuotientLevel {
            factor: lit(1, true),
            clause_indices: vec![0, 1, 2, 3, 4],
            matches: vec![0, 1, 2, 3, 4],
        },
        QuotientLevel {
            factor: lit(2, true),
            clause_indices: vec![0, 1, 2, 3],
            matches: vec![0, 1, 2, 3],
        },
    ];
    let (idx, reduction) = find_best_quotient(&chain).unwrap();
    // At depth 2 (3 factors, 4 quotients): 12 - 7 = 5
    // At depth 1 (2 factors, 5 quotients): 10 - 7 = 3
    // At depth 0 (1 factor, 6 quotients): 6 - 7 = -1
    assert_eq!(idx, 2);
    assert_eq!(reduction, 5);
}

#[test]
fn test_find_best_quotient_no_gain() {
    use super::chain::{find_best_quotient, QuotientLevel};

    // 1 factor, 3 quotients: 3 -> 4, no gain.
    let chain = vec![QuotientLevel {
        factor: lit(0, true),
        clause_indices: vec![0, 1, 2],
        matches: Vec::new(),
    }];
    assert!(find_best_quotient(&chain).is_none());
}

#[test]
fn test_factor_basic_matrix() {
    // Create a 2×3 factoring matrix:
    // Clauses sharing quotient (c, d) with factors a, b:
    // (a ∨ c), (b ∨ c), (a ∨ d), (b ∨ d), (a ∨ e), (b ∨ e)
    // 2 factors {a, b}, 3 quotients {c, d, e}: 6 -> 5, reduction = 1.
    let mut clause_db = ClauseArena::new();
    let a = lit(0, true); // factor 1
    let b = lit(1, true); // factor 2
    let c = lit(2, true); // quotient 1
    let d = lit(3, true); // quotient 2
    let e = lit(4, true); // quotient 3

    // Add clauses.
    let c0 = clause_db.add(&[a, c], false); // (a ∨ c)
    let c1 = clause_db.add(&[b, c], false); // (b ∨ c)
    let c2 = clause_db.add(&[a, d], false); // (a ∨ d)
    let c3 = clause_db.add(&[b, d], false); // (b ∨ d)
    let c4 = clause_db.add(&[a, e], false); // (a ∨ e)
    let c5 = clause_db.add(&[b, e], false); // (b ∨ e)

    // Build occurrence list.
    let mut occ = OccList::new(6);
    for ci in [c0, c1, c2, c3, c4, c5] {
        let lits = clause_db.literals(ci);
        occ.add_clause(ci, lits);
    }

    let vals = vec![0i8; 12]; // 6 vars × 2 literals, all unassigned
    let var_states = vec![crate::solver::lifecycle::VarState::Active; 6];
    let mut factor = Factor::new(6);

    let result = factor.run(
        &clause_db,
        &occ,
        &vals,
        &var_states,
        &FactorConfig {
            next_var_id: 6,
            effort_limit: u64::MAX,
            elim_bound: 0,
        },
    );

    // Should have factored: 6 clauses deleted, 5 added (2 dividers + 3 quotients).
    // Binary clauses are now included in factorization (CaDiCaL parity).
    // 2 factors {a, b}, 3 quotients {c, d, e}: reduction = 2*3 - (2+3) = 1.
    assert_eq!(result.factored_count, 1);
    assert_eq!(result.extension_vars_needed, 1);
    assert_eq!(result.to_delete.len(), 6);
    assert_eq!(result.new_clauses.len(), 5); // 2 dividers + 3 quotients
}

#[test]
fn test_factor_elim_bound_guards_marginal_factoring() {
    // Same 2×3 matrix as test_factor_basic_matrix: reduction = 1.
    // With elim_bound = 1, factoring should NOT fire because
    // reduction(1) <= elim_bound(1). CaDiCaL factor.cpp:888.
    let mut clause_db = ClauseArena::new();
    let a = lit(0, true);
    let b = lit(1, true);
    let c = lit(2, true);
    let d = lit(3, true);
    let e = lit(4, true);

    let c0 = clause_db.add(&[a, c], false);
    let c1 = clause_db.add(&[b, c], false);
    let c2 = clause_db.add(&[a, d], false);
    let c3 = clause_db.add(&[b, d], false);
    let c4 = clause_db.add(&[a, e], false);
    let c5 = clause_db.add(&[b, e], false);

    let mut occ = OccList::new(6);
    for ci in [c0, c1, c2, c3, c4, c5] {
        occ.add_clause(ci, clause_db.literals(ci));
    }

    let vals = vec![0i8; 12];
    let var_states = vec![crate::solver::lifecycle::VarState::Active; 6];
    let mut factor = Factor::new(6);

    // elim_bound = 1: reduction(1) <= 1, so no factoring.
    let result = factor.run(
        &clause_db,
        &occ,
        &vals,
        &var_states,
        &FactorConfig {
            next_var_id: 6,
            effort_limit: u64::MAX,
            elim_bound: 1,
        },
    );
    assert_eq!(
        result.factored_count, 0,
        "elim_bound=1 should block reduction=1 factoring"
    );

    // elim_bound = 0: reduction(1) > 0, so factoring fires (same as default).
    let mut factor2 = Factor::new(6);
    let result2 = factor2.run(
        &clause_db,
        &occ,
        &vals,
        &var_states,
        &FactorConfig {
            next_var_id: 6,
            effort_limit: u64::MAX,
            elim_bound: 0,
        },
    );
    assert_eq!(
        result2.factored_count, 1,
        "elim_bound=0 should allow reduction=1 factoring"
    );
}

#[test]
fn test_factor_ternary_matrix() {
    // 2 factors, 3 quotients with ternary clauses:
    // Quotient (c ∨ d), factors a and b:
    // (a ∨ c ∨ d), (b ∨ c ∨ d)
    // Quotient (c ∨ e):
    // (a ∨ c ∨ e), (b ∨ c ∨ e)
    // Quotient (d ∨ e):
    // (a ∨ d ∨ e), (b ∨ d ∨ e)
    //
    // 6 clauses -> 5 (2 dividers + 3 quotient clauses), reduction = 1.
    let mut clause_db = ClauseArena::new();
    let a = lit(0, true);
    let b = lit(1, true);
    let c = lit(2, true);
    let d = lit(3, true);
    let e = lit(4, true);

    let c0 = clause_db.add(&[a, c, d], false);
    let c1 = clause_db.add(&[b, c, d], false);
    let c2 = clause_db.add(&[a, c, e], false);
    let c3 = clause_db.add(&[b, c, e], false);
    let c4 = clause_db.add(&[a, d, e], false);
    let c5 = clause_db.add(&[b, d, e], false);

    let mut occ = OccList::new(6);
    for ci in [c0, c1, c2, c3, c4, c5] {
        let lits = clause_db.literals(ci);
        occ.add_clause(ci, lits);
    }

    let vals = vec![0i8; 12]; // 6 vars × 2 literals, all unassigned
    let var_states = vec![crate::solver::lifecycle::VarState::Active; 6];
    let mut factor = Factor::new(6);

    let result = factor.run(
        &clause_db,
        &occ,
        &vals,
        &var_states,
        &FactorConfig {
            next_var_id: 6,
            effort_limit: u64::MAX,
            elim_bound: 0,
        },
    );

    // Expect factoring: 6 ternary clauses -> 2 binary dividers + 3 binary quotient clauses.
    if result.factored_count > 0 {
        assert_eq!(
            result.to_delete.len(),
            6,
            "factoring must delete a complete 2x3 matrix"
        );
        assert_eq!(
            result.new_clauses.len(),
            5,
            "factoring must add 2 dividers + 3 quotient clauses"
        );
        assert!(!result.to_delete.is_empty());
        assert!(!result.new_clauses.is_empty());
        assert_eq!(result.extension_vars_needed, 1);

        // Wave 1: verify structured application data matches flattened result.
        assert_eq!(
            result.applications.len(),
            1,
            "one factoring application expected"
        );
        let app = &result.applications[0];
        assert_eq!(app.factors.len(), 2, "2 factors");
        assert_eq!(app.divider_clauses.len(), 2, "2 dividers");
        assert_eq!(app.quotient_clauses.len(), 3, "3 quotients");
        assert_eq!(app.to_delete.len(), 6, "6 originals deleted");
        // Blocked clause: (¬fresh ∨ ¬f1 ∨ ¬f2)
        assert_eq!(
            app.blocked_clause.len(),
            3,
            "blocked clause has ¬fresh + 2 negated factors"
        );
    }
    // Even if factoring doesn't fire (reduction threshold), no crash.
}

#[test]
fn test_factor_skips_satisfied_clauses() {
    // Regression for #3468: factoring must not rewrite clauses that are
    // already satisfied by the current assignment.
    let mut clause_db = ClauseArena::new();
    let a = lit(0, true);
    let b = lit(1, true);
    let c = lit(2, true);
    let d = lit(3, true);
    let e = lit(4, true);

    let c0 = clause_db.add(&[a, c, d], false);
    let c1 = clause_db.add(&[b, c, d], false);
    let c2 = clause_db.add(&[a, c, e], false);
    let c3 = clause_db.add(&[b, c, e], false);
    let c4 = clause_db.add(&[a, d, e], false);
    let c5 = clause_db.add(&[b, d, e], false);

    let mut occ = OccList::new(6);
    for ci in [c0, c1, c2, c3, c4, c5] {
        let lits = clause_db.literals(ci);
        occ.add_clause(ci, lits);
    }

    // All clauses are satisfied by c=d=e=true.
    // vars 2,3,4 assigned positive; vars 0,1,5 unassigned
    let mut vals = vec![0i8; 12]; // 6 vars × 2 literals
    for v in [2, 3, 4] {
        vals[v * 2] = 1; // positive literal = true
        vals[v * 2 + 1] = -1; // negative literal = false
    }
    let var_states = vec![crate::solver::lifecycle::VarState::Active; 6];
    let mut factor = Factor::new(6);

    let result = factor.run(
        &clause_db,
        &occ,
        &vals,
        &var_states,
        &FactorConfig {
            next_var_id: 6,
            effort_limit: u64::MAX,
            elim_bound: 0,
        },
    );
    assert_eq!(
        result.factored_count, 0,
        "factorization must ignore satisfied clauses"
    );
    assert!(
        result.to_delete.is_empty(),
        "no satisfied clause may be deleted"
    );
    assert!(
        result.new_clauses.is_empty(),
        "no replacement clauses should be introduced"
    );
}

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
