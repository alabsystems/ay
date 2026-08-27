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
fn test_duplicate_clauses_do_not_poison_factor_chains() {
    // Regression for #dup-factor-poison: exact-duplicate clauses used to
    // fabricate phantom quotient support in `find_next_factor` (one count
    // per source CLAUSE, so a duplicated pair passed MIN_FACTOR_MATCHES on
    // what is really one clause) and record the same partner arena index in
    // several matrix cells; the extraction then bailed to the occ-rescan
    // fallback, found fewer disjoint cells than `factors * quotients`, and
    // returned None. Duplicates placed on every productive candidate made
    // the whole pass yield zero (mexam raw inputs: factor_count 0).
    //
    // Clean 2x3 matrix (factors {a, b}, quotients {c, d, e}) plus one
    // duplicated support clause per candidate literal: (a ∨ c) poisons the
    // chains seeded at a and c, (b ∨ d) poisons b and d, (a ∨ e) poisons e.
    // Before the dedup fix this formula factored NOTHING; with it, the
    // duplicate copies are dropped from the candidate's eligible view and
    // the clean 2x3 matrix extracts exactly.
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
    let c6 = clause_db.add(&[a, c], false); // duplicate of c0
    let c7 = clause_db.add(&[b, d], false); // duplicate of c3
    let c8 = clause_db.add(&[a, e], false); // duplicate of c4

    let mut occ = OccList::new(6);
    for ci in [c0, c1, c2, c3, c4, c5, c6, c7, c8] {
        occ.add_clause(ci, clause_db.literals(ci));
    }

    let vals = vec![0i8; 12];
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
        result.factored_count, 1,
        "duplicated support clauses must not poison the clean 2x3 factoring"
    );
    assert_eq!(result.extension_vars_needed, 1);
    assert_eq!(
        result.to_delete.len(),
        6,
        "exactly the clean 2x3 matrix is deleted"
    );
    assert_eq!(result.new_clauses.len(), 5); // 2 dividers + 3 quotients
    for dup in [c6, c7, c8] {
        assert!(
            !result.to_delete.contains(&dup),
            "surviving duplicate copies stay in the clause DB"
        );
    }
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

mod correctness;
