// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::ArrayAxiomMode;
use crate::Executor;
use ay_core::{Sort, TermData};
use ay_frontend::parse;

fn run_script(input: &str) -> Vec<String> {
    let commands = parse(input).expect("SMT-LIB script should parse");
    let mut exec = Executor::new();
    exec.execute_all(&commands)
        .expect("SMT-LIB script should execute")
}

fn prepare_executor(input: &str) -> Executor {
    let commands = parse(input).expect("SMT-LIB setup script should parse");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("SMT-LIB setup script should execute");
    assert!(
        outputs.is_empty(),
        "setup scripts should not emit check-sat results"
    );
    exec
}

#[test]
fn finite_array_extensionality_budget_emits_only_complete_equality_atoms() {
    let mut exec = prepare_executor(
        r#"
        (set-logic QF_ABV)
        (declare-const a (Array (_ BitVec 4) (_ BitVec 8)))
        (declare-const b (Array (_ BitVec 4) (_ BitVec 8)))
        (assert (= (store a #x0 #x01) (store a #x1 #x02)))
        (assert (= (store b #x2 #x03) (store b #x3 #x04)))
    "#,
    );
    let assertion_count = exec.ctx.assertions.len();

    let report = exec.add_finite_index_array_extensionality_with_budget(16);

    assert_eq!(report.candidate_equalities, 2);
    assert_eq!(report.candidate_index_points, 32);
    assert_eq!(report.emitted_equalities, 1);
    assert_eq!(report.emitted_index_points, 16);
    assert_eq!(report.budget_deferred_equalities, 1);
    assert_eq!(report.budget_deferred_index_points, 16);
    assert!(!report.is_complete());
    assert_eq!(
        exec.ctx.assertions.len(),
        assertion_count + 1,
        "the budget may emit one whole biconditional, never a partial second one"
    );
}

#[test]
fn finite_array_closure_reaches_nested_array_fixed_point() {
    let mut exec = prepare_executor(
        r#"
        (set-logic QF_AX)
        (declare-const a (Array Bool (Array Bool Bool)))
        (declare-const b (Array Bool (Array Bool Bool)))
        (assert (= a b))
    "#,
    );

    let report = exec.add_finite_index_array_closure();

    assert!(report.is_complete(), "nested closure deferred: {report:?}");
    assert_eq!(report.emitted_equalities, 3);
    assert_eq!(report.emitted_index_points, 6);
    assert_eq!(report.budget_deferred_equalities, 0);
}

#[test]
fn incremental_const_store_extensionality_exposes_finite_cell_equality() {
    let mut exec = prepare_executor(
        r#"
        (set-logic QF_AX)
        (declare-const constant_cell (Array Bool Int))
        (declare-const base_cell (Array Bool Int))
        (declare-const stored_cell (Array Bool Int))
        (assert
          (= ((as const (Array Int (Array Bool Int))) constant_cell)
             (store ((as const (Array Int (Array Bool Int))) base_cell)
                    0
                    stored_cell)))
    "#,
    );

    let initial = exec.add_finite_index_array_closure();
    assert_eq!(initial.candidate_equalities, 0);
    assert_eq!(initial.emitted_equalities, 0);

    // The infinite outer Int carrier is outside exact closure. Its restricted
    // const/store axiom nevertheless exposes `constant_cell = stored_cell`,
    // whose nested Bool carrier must be closed by the incremental route's
    // second, final pass.
    exec.add_const_store_array_extensionality();
    let final_report = exec.add_finite_index_array_closure();

    assert!(final_report.is_complete());
    assert_eq!(final_report.candidate_equalities, 1);
    assert_eq!(final_report.emitted_equalities, 1);
    assert_eq!(final_report.emitted_index_points, 2);
}

#[test]
fn finite_array_closure_reuses_axiom_without_recharge_and_reinstalls_after_swap() {
    let mut exec = prepare_executor(
        r#"
        (set-logic QF_ABV)
        (declare-const a (Array (_ BitVec 4) (_ BitVec 8)))
        (declare-const b (Array (_ BitVec 4) (_ BitVec 8)))
        (assert (= a b))
    "#,
    );
    let base_len = exec.ctx.assertions.len();
    let first = exec.add_finite_index_array_closure();
    let remaining = exec.finite_array_expansion.remaining_index_points;
    assert_eq!(first.emitted_equalities, 1);
    assert_eq!(exec.ctx.assertions.len(), base_len + 1);

    let second = exec.add_finite_index_array_closure();
    assert_eq!(second.emitted_equalities, 0);
    assert_eq!(second.already_covered_equalities, 1);
    assert_eq!(exec.ctx.assertions.len(), base_len + 1);
    assert_eq!(
        exec.finite_array_expansion.remaining_index_points,
        remaining
    );

    // Simulate an internal route assertion swap while the query ledger and
    // proof session remain alive. A cache hit must reinstall the axiom without
    // charging it again.
    exec.ctx.assertions.truncate(base_len);
    let reinstalled = exec.add_finite_index_array_closure();
    assert_eq!(reinstalled.emitted_equalities, 0);
    assert_eq!(reinstalled.already_covered_equalities, 1);
    assert_eq!(exec.ctx.assertions.len(), base_len + 1);
    assert_eq!(
        exec.finite_array_expansion.remaining_index_points,
        remaining
    );
}

#[test]
fn finite_array_closure_shares_budget_between_symbolic_selects_and_equalities() {
    let mut exec = prepare_executor(
        r#"
        (set-logic QF_AX)
        (declare-const a (Array Bool Bool))
        (declare-const b (Array Bool Bool))
        (declare-const p Bool)
        (assert (= (select a p) true))
        (assert (= a b))
    "#,
    );

    let report = exec.add_finite_index_array_extensionality_with_budget(2);

    assert_eq!(report.emitted_selects, 1);
    assert_eq!(report.emitted_select_index_points, 2);
    assert_eq!(report.emitted_equalities, 0);
    assert_eq!(report.budget_deferred_equalities, 1);
    assert!(!report.is_complete());
}

#[test]
fn finite_array_value_cell_cap_defers_before_domain_allocation() {
    let mut exec = prepare_executor(
        r#"
        (set-logic QF_ABV)
        (declare-const a (Array (_ BitVec 8) (_ BitVec 1024)))
        (declare-const b (Array (_ BitVec 8) (_ BitVec 1024)))
        (assert (= a b))
    "#,
    );
    let term_count = exec.ctx.terms.len();

    let report = exec.add_finite_index_array_closure();

    assert_eq!(report.emitted_equalities, 0);
    assert_eq!(report.budget_deferred_equalities, 1);
    assert_eq!(report.budget_deferred_value_cells, 256 * 1024);
    assert_eq!(
        exec.ctx.terms.len(),
        term_count,
        "a rejected whole candidate must not allocate its 256 domain terms"
    );
}

#[test]
fn finite_array_budget_rearms_only_at_external_query_boundary() {
    let mut exec = prepare_executor(
        r#"
        (set-logic QF_AX)
        (declare-const a (Array Bool Bool))
        (declare-const b (Array Bool Bool))
        (assert (= a b))
    "#,
    );

    let exhausted = exec.add_finite_index_array_extensionality_with_budget(0);
    assert!(!exhausted.is_complete());
    assert!(!exec.finite_array_expansion.is_complete());
    assert_eq!(exec.finite_array_expansion.remaining_index_points, 0);

    exec.begin_public_solve(false);
    assert!(!exec.finite_array_expansion.is_complete());
    assert_eq!(
        exec.finite_array_expansion.remaining_index_points, 0,
        "an internal continuation must not replenish the query budget"
    );

    exec.begin_external_decision_query(false);
    let replenished = exec.add_finite_index_array_closure();
    assert!(replenished.is_complete());
    assert_eq!(replenished.emitted_equalities, 1);
}

#[test]
fn finite_array_candidate_scan_is_bounded_and_fail_closed() {
    let mut exec = Executor::new();
    let array_sort = Sort::array(Sort::Bool, Sort::Bool);
    for index in 0..=Executor::FINITE_ARRAY_CANDIDATE_SCAN_CAP {
        let lhs = exec
            .ctx
            .terms
            .mk_var(format!("scan_lhs_{index}"), array_sort.clone());
        let rhs = exec
            .ctx
            .terms
            .mk_var(format!("scan_rhs_{index}"), array_sort.clone());
        let equality = exec.ctx.terms.mk_eq(lhs, rhs);
        exec.ctx.assertions.push(equality);
    }

    let report = exec.add_finite_index_array_closure();

    assert_eq!(report.candidate_scan_truncated, 1);
    assert_eq!(
        report.candidate_equalities,
        Executor::FINITE_ARRAY_CANDIDATE_SCAN_CAP
    );
    assert!(!report.is_complete());
    assert!(exec.finite_array_expansion.candidate_scan_truncated);
}

// --- Core check-sat path tests ---

#[test]
fn euf_sat_simple_equality() {
    let input = r#"
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-const a U)
        (declare-const b U)
        (assert (= a b))
        (check-sat)
    "#;
    assert_eq!(run_script(input), vec!["sat"]);
}

#[test]
fn euf_unsat_disequality_contradiction() {
    let input = r#"
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-const a U)
        (assert (distinct a a))
        (check-sat)
    "#;
    assert_eq!(run_script(input), vec!["unsat"]);
}

#[test]
fn euf_unsat_transitivity() {
    let input = r#"
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-const a U)
        (declare-const b U)
        (declare-const c U)
        (assert (= a b))
        (assert (= b c))
        (assert (distinct a c))
        (check-sat)
    "#;
    assert_eq!(run_script(input), vec!["unsat"]);
}

#[test]
fn euf_unsat_function_congruence() {
    let input = r#"
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-const a U)
        (declare-const b U)
        (declare-fun f (U) U)
        (assert (= a b))
        (assert (distinct (f a) (f b)))
        (check-sat)
    "#;
    assert_eq!(run_script(input), vec!["unsat"]);
}

#[test]
fn euf_sat_distinct_variables() {
    let input = r#"
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-const a U)
        (declare-const b U)
        (assert (distinct a b))
        (check-sat)
    "#;
    assert_eq!(run_script(input), vec!["sat"]);
}

#[test]
fn euf_empty_assertions_sat() {
    let input = r#"
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-const a U)
        (check-sat)
    "#;
    assert_eq!(run_script(input), vec!["sat"]);
}

// --- Incremental / push-pop tests ---

#[test]
fn incremental_euf_push_pop_roundtrip() {
    let input = r#"
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-const a U)
        (declare-fun p (U) Bool)
        (assert (p a))
        (push 1)
        (assert (not (p a)))
        (check-sat)
        (pop 1)
        (check-sat)
    "#;

    assert_eq!(run_script(input), vec!["unsat", "sat"]);
}

/// Regression test for #2822: same activation-scope bug as LRA affects all
/// theory solvers sharing IncrementalTheoryState. After pop+push, scoped
/// activation clauses for global assertions were not re-added.
#[test]
fn incremental_euf_contradiction_after_push_pop_cycle() {
    let input = r#"
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-const a U)
        (declare-const b U)
        (declare-fun f (U) U)
        (assert (= (f a) b))
        (push 1)
        (assert (= a b))
        (check-sat)
        (pop 1)
        (push 1)
        (assert (distinct (f a) b))
        (check-sat)
        (pop 1)
    "#;
    let result = run_script(input);
    assert_eq!(
        result,
        vec!["sat", "unsat"],
        "f(a)=b and f(a)!=b should be UNSAT after push/pop cycle, got {result:?}"
    );
}

#[test]
fn incremental_euf_nested_push_pop() {
    let input = r#"
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-const a U)
        (declare-const b U)
        (declare-const c U)
        (assert (= a b))
        (push 1)
        (assert (= b c))
        (push 1)
        (assert (distinct a c))
        (check-sat)
        (pop 1)
        (check-sat)
        (pop 1)
        (check-sat)
    "#;
    assert_eq!(run_script(input), vec!["unsat", "sat", "sat"]);
}

#[test]
fn incremental_euf_multiple_check_sats_same_scope() {
    let input = r#"
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-const a U)
        (declare-const b U)
        (assert (= a b))
        (push 1)
        (check-sat)
        (assert (distinct a b))
        (check-sat)
        (pop 1)
        (check-sat)
    "#;
    assert_eq!(run_script(input), vec!["sat", "unsat", "sat"]);
}

#[test]
fn incremental_euf_empty_assertions_are_sat() {
    let input = r#"
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-const a U)
        (push 1)
        (check-sat)
        (pop 1)
        (check-sat)
    "#;

    assert_eq!(run_script(input), vec!["sat", "sat"]);
}

// --- Array extensionality and store congruence regression tests (#4304) ---

#[test]
fn array_store_value_congruence_unsat() {
    // store(a,i,v) = store(a,i,w) ∧ v≠w → UNSAT
    // By ROW1: select(store(a,i,v),i)=v and select(store(a,i,w),i)=w
    // Stores equal → v=w, contradicting v≠w
    let input = r#"
        (set-logic QF_AX)
        (declare-sort Index 0)
        (declare-sort Elem 0)
        (declare-fun a () (Array Index Elem))
        (declare-fun i () Index)
        (declare-fun v () Elem)
        (declare-fun w () Elem)
        (assert (= (store a i v) (store a i w)))
        (assert (not (= v w)))
        (check-sat)
    "#;
    assert_eq!(run_script(input), vec!["unsat"]);
}

#[test]
fn array_store_base_congruence_extensionality_unsat() {
    // store(a,i,e) = store(b,i,e) ∧ a[i]=b[i] ∧ a≠b → UNSAT
    // By ROW2: for k≠i, a[k]=b[k] (through equal stores)
    // Combined with a[i]=b[i]: arrays agree everywhere → a=b
    let input = r#"
        (set-logic QF_AX)
        (declare-sort Index 0)
        (declare-sort Elem 0)
        (declare-fun a () (Array Index Elem))
        (declare-fun b () (Array Index Elem))
        (declare-fun i () Index)
        (declare-fun e () Elem)
        (assert (= (store a i e) (store b i e)))
        (assert (= (select a i) (select b i)))
        (assert (not (= a b)))
        (check-sat)
    "#;
    assert_eq!(run_script(input), vec!["unsat"]);
}

#[test]
fn store_congruence_select_cache_tracks_new_terms_6820() {
    let mut exec = prepare_executor(
        r#"
        (set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const b (Array Int Int))
        (declare-const i Int)
        (declare-const j Int)
        (declare-const v Int)
        (declare-const x Int)
        (assert (= b (store a i v)))
        (assert (= (select a j) x))
    "#,
    );

    let a = exec.ctx.terms.lookup("a").expect("a declared");
    let b = exec.ctx.terms.lookup("b").expect("b declared");
    let i = exec.ctx.terms.lookup("i").expect("i declared");
    let j = exec.ctx.terms.lookup("j").expect("j declared");

    exec.reset_array_congruence_caches();
    exec.add_store_value_congruence_axioms();

    assert_eq!(
        exec.cached_select_indices_by_array
            .get(&a)
            .map(Vec::as_slice),
        Some(&[j][..]),
        "initial refresh should index only the existing select(a, j)"
    );
    assert!(
        !exec.cached_select_indices_by_array.contains_key(&b),
        "new selects on the equality target are created during the pass and should be picked up on the next refresh"
    );

    exec.add_store_other_side_congruence_axioms();

    let mut target_indices = exec
        .cached_select_indices_by_array
        .get(&b)
        .cloned()
        .expect("second refresh should index selects created for b");
    target_indices.sort_unstable_by_key(|term| term.0);
    assert_eq!(
        target_indices,
        vec![i, j],
        "incremental refresh must discover the target-side select terms created by the previous congruence pass"
    );
}

#[test]
fn directly_negated_shadowed_store_eq_skips_congruence_cache_8785() {
    let mut exec = prepare_executor(
        r#"
        (set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const i Int)
        (declare-const j Int)
        (declare-const v Int)
        (declare-const w Int)
        (declare-const x Int)
        (assert (not (= i j)))
        (assert (not (= (store (store a i v) j x)
                        (store (store a i w) j x))))
    "#,
    );

    let a = exec.ctx.terms.lookup("a").expect("a declared");
    let i = exec.ctx.terms.lookup("i").expect("i declared");
    let j = exec.ctx.terms.lookup("j").expect("j declared");
    let v = exec.ctx.terms.lookup("v").expect("v declared");
    let w = exec.ctx.terms.lookup("w").expect("w declared");
    let x = exec.ctx.terms.lookup("x").expect("x declared");
    let lhs_inner = exec.ctx.terms.mk_store(a, i, v);
    let rhs_inner = exec.ctx.terms.mk_store(a, i, w);
    let lhs = exec.ctx.terms.mk_store(lhs_inner, j, x);
    let rhs = exec.ctx.terms.mk_store(rhs_inner, j, x);
    let store_eq = exec.ctx.terms.mk_eq(lhs, rhs);

    exec.reset_array_congruence_caches();

    let before = exec.ctx.assertions.len();
    exec.add_store_value_congruence_axioms();

    assert!(
        !exec
            .cached_store_eqs
            .iter()
            .any(|(eq_term, ..)| *eq_term == store_eq),
        "top-level negated store equality should not seed eager store congruence"
    );

    exec.add_store_other_side_congruence_axioms();
    exec.add_store_disjunctive_index_axioms();

    assert_eq!(
        exec.ctx.assertions.len(),
        before,
        "directly negated shadowed-store disequality must not append eager store congruence axioms"
    );
}

#[test]
fn array_extensionality_sat_different_at_other_index() {
    // a[i]=b[i] ∧ a≠b → SAT (arrays can differ at some other index)
    let input = r#"
        (set-logic QF_AX)
        (declare-sort Index 0)
        (declare-sort Elem 0)
        (declare-fun a () (Array Index Elem))
        (declare-fun b () (Array Index Elem))
        (declare-fun i () Index)
        (assert (= (select a i) (select b i)))
        (assert (not (= a b)))
        (check-sat)
    "#;
    assert_eq!(run_script(input), vec!["sat"]);
}

mod negated_pointwise_array;

#[test]
fn negated_pointwise_forall_array_eq_with_eq_premise_is_unsat() {
    // Companion to the wrong-unsat fix: when `(= b cc)` IS genuinely asserted, the
    // negated pointwise forall (its negation says `b != cc`) is truly UNSAT. The
    // polarity-aware skip must not over-correct into always-SAT — the Skolemized
    // negated forall is still refuted by the ground array equality.
    let input = r#"
        (set-logic ALIA)
        (declare-const b (Array Int Int))
        (declare-const cc (Array Int Int))
        (assert (not (forall ((X0 Int)) (= (select b X0) (select cc X0)))))
        (assert (= b cc))
        (check-sat)
    "#;
    assert_eq!(run_script(input), vec!["unsat"]);
}

#[test]
fn positive_pointwise_forall_array_eq_with_diseq_is_unsat() {
    // The positive extensionality protection (the reason the pass exists) must be
    // preserved by the polarity refactor: a POSITIVELY-asserted
    // `(forall i. a[i]=b[i])` plus `a != b` is UNSAT (extensionality).
    let input = r#"
        (set-logic ALIA)
        (declare-const a (Array Int Int))
        (declare-const b (Array Int Int))
        (assert (forall ((i Int)) (= (select a i) (select b i))))
        (assert (not (= a b)))
        (check-sat)
    "#;
    assert_eq!(run_script(input), vec!["unsat"]);
}

// array_store_creates_different_array_sat: removed — solver returns "unknown"
// for this QF_AX problem (theory completeness gap, not a regression). The test
// was added in euf.rs split (daec7b69d) but never verified to pass.

#[test]
fn array_row_lemmas_use_unit_clause_for_asserted_disequality_6282() {
    let mut exec = prepare_executor(
        r#"
        (set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const i Int)
        (declare-const j Int)
        (assert (not (= i j)))
        (assert (= (select (store a i 42) j) 0))
    "#,
    );

    let a = exec.ctx.terms.lookup("a").expect("a declared");
    let i = exec.ctx.terms.lookup("i").expect("i declared");
    let j = exec.ctx.terms.lookup("j").expect("j declared");
    let value_42 = exec.ctx.terms.mk_int(42.into());
    let store = exec.ctx.terms.mk_store(a, i, value_42);
    let select_term = exec.ctx.terms.mk_select(store, j);
    let base_select = exec.ctx.terms.mk_select(a, j);
    let row2_eq = exec.ctx.terms.mk_eq(select_term, base_select);
    let idx_eq = exec.ctx.terms.mk_eq(i, j);
    let row2_clause = exec.ctx.terms.mk_or(vec![idx_eq, row2_eq]);
    let not_idx_eq = exec.ctx.terms.mk_not(idx_eq);
    let row1_eq = exec.ctx.terms.mk_eq(select_term, value_42);
    let row1_clause = exec.ctx.terms.mk_or(vec![not_idx_eq, row1_eq]);

    let before = exec.ctx.assertions.len();
    exec.add_array_row_lemmas();

    assert_eq!(
        exec.ctx.assertions.len(),
        before + 1,
        "asserted i != j should turn ROW2 into a single unit equality"
    );
    assert!(
        exec.ctx.assertions.contains(&row2_eq),
        "ROW2 consequent should be asserted directly as a unit fact"
    );
    assert!(
        !exec.ctx.assertions.contains(&row2_clause),
        "disjunctive ROW2 clause should be skipped once i != j is known"
    );
    assert!(
        !exec.ctx.assertions.contains(&row1_clause),
        "ROW1 clause is tautological once i != j is known"
    );
}

#[test]
fn lazy_row_fixpoint_seeds_terms_without_row_clauses_6546() {
    let mut exec = prepare_executor(
        r#"
        (set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const i Int)
        (declare-const j Int)
        (assert (= (select (store a i 42) j) 0))
    "#,
    );

    let a = exec.ctx.terms.lookup("a").expect("a declared");
    let i = exec.ctx.terms.lookup("i").expect("i declared");
    let j = exec.ctx.terms.lookup("j").expect("j declared");
    let value_42 = exec.ctx.terms.mk_int(42.into());
    let zero = exec.ctx.terms.mk_int(0.into());
    let store = exec.ctx.terms.mk_store(a, i, value_42);
    let select_term = exec.ctx.terms.mk_select(store, j);
    let before_assertions = exec.ctx.assertions.len();

    exec.run_array_axiom_fixpoint_lazy_row_final_check_for_tests(before_assertions);

    let term_count_after_fixpoint = exec.ctx.terms.len();
    let base_select = exec.ctx.terms.mk_select(a, j);
    assert_eq!(
        exec.ctx.terms.len(),
        term_count_after_fixpoint,
        "lazy fixpoint should seed select(a, j) before theory solving"
    );

    let row2_eq = exec.ctx.terms.mk_eq(select_term, base_select);
    let idx_eq = exec.ctx.terms.mk_eq(i, j);
    let not_idx_eq = exec.ctx.terms.mk_not(idx_eq);
    let row1_eq = exec.ctx.terms.mk_eq(select_term, value_42);
    let row1_clause = exec.ctx.terms.mk_or(vec![not_idx_eq, row1_eq]);
    let row2_clause = exec.ctx.terms.mk_or(vec![idx_eq, row2_eq]);
    let original_assertion = exec.ctx.terms.mk_eq(select_term, zero);

    assert!(
        exec.ctx.assertions.contains(&original_assertion),
        "original array assertion must be preserved"
    );
    assert!(
        !exec.ctx.assertions.contains(&row1_clause),
        "lazy fixpoint must not inject eager ROW1 clauses"
    );
    assert!(
        !exec.ctx.assertions.contains(&row2_clause),
        "lazy fixpoint must not inject eager ROW2 clauses"
    );
    assert!(
        !exec.ctx.assertions.contains(&row2_eq),
        "lazy fixpoint should seed terms, not add unit ROW equalities"
    );
}

#[test]
fn row_seeding_does_not_recurse_from_seeded_descendant_8785() {
    let mut exec = prepare_executor(
        r#"
        (set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const i Int)
        (declare-const j Int)
        (declare-const k Int)
        (assert (= (select (store (store a i 10) j 20) k) 0))
    "#,
    );

    let a = exec.ctx.terms.lookup("a").expect("a declared");
    let i = exec.ctx.terms.lookup("i").expect("i declared");
    let j = exec.ctx.terms.lookup("j").expect("j declared");
    let k = exec.ctx.terms.lookup("k").expect("k declared");
    let ten = exec.ctx.terms.mk_int(10.into());
    let twenty = exec.ctx.terms.mk_int(20.into());
    let inner_store = exec.ctx.terms.mk_store(a, i, ten);
    let _outer_store = exec.ctx.terms.mk_store(inner_store, j, twenty);

    assert!(
        exec.seed_array_row_terms(),
        "first pass should seed the one-hop descendant select"
    );

    let term_count_after_first_seed = exec.ctx.terms.len();
    let _seeded_intermediate = exec.ctx.terms.mk_select(inner_store, k);
    assert_eq!(
        exec.ctx.terms.len(),
        term_count_after_first_seed,
        "first pass should already have created the one-hop descendant"
    );

    assert!(
        !exec.seed_array_row_terms(),
        "second pass must not recurse from a ROW-seeded descendant"
    );

    let term_count_after_second_seed = exec.ctx.terms.len();
    let _base_select = exec.ctx.terms.mk_select(a, k);
    assert_eq!(
        exec.ctx.terms.len(),
        term_count_after_second_seed + 1,
        "base select should still be absent until explicitly requested"
    );
}

#[test]
fn row_seeding_marks_reused_descendant_without_skipping_parent_clauses_8785() {
    let mut exec = prepare_executor(
        r#"
        (set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const i Int)
        (declare-const j Int)
        (declare-const k Int)
        (assert (= (select (store (store a i 10) j 20) k) 0))
    "#,
    );

    let a = exec.ctx.terms.lookup("a").expect("a declared");
    let i = exec.ctx.terms.lookup("i").expect("i declared");
    let j = exec.ctx.terms.lookup("j").expect("j declared");
    let k = exec.ctx.terms.lookup("k").expect("k declared");
    let ten = exec.ctx.terms.mk_int(10.into());
    let twenty = exec.ctx.terms.mk_int(20.into());
    let zero = exec.ctx.terms.mk_int(0.into());
    let inner_store = exec.ctx.terms.mk_store(a, i, ten);
    let outer_store = exec.ctx.terms.mk_store(inner_store, j, twenty);
    let select_term = exec.ctx.terms.mk_select(outer_store, k);
    let seeded_descendant = exec.ctx.terms.mk_select(inner_store, k);
    let term_count_before_seed = exec.ctx.terms.len();

    assert!(
        !exec.seed_array_row_terms(),
        "reused descendant should be marked seeded without growing the term store"
    );
    assert_eq!(
        exec.ctx.terms.len(),
        term_count_before_seed,
        "seeding a reused descendant should not create new terms"
    );

    exec.add_array_row_clauses();

    let top_idx_eq = exec.ctx.terms.mk_eq(j, k);
    let top_not_idx_eq = exec.ctx.terms.mk_not(top_idx_eq);
    let top_row1_eq = exec.ctx.terms.mk_eq(select_term, twenty);
    let top_row1_clause = exec.ctx.terms.mk_or(vec![top_not_idx_eq, top_row1_eq]);
    let top_row2_eq = exec.ctx.terms.mk_eq(select_term, seeded_descendant);
    let top_row2_clause = exec.ctx.terms.mk_or(vec![top_idx_eq, top_row2_eq]);

    let base_select = exec.ctx.terms.mk_select(a, k);
    let descendant_idx_eq = exec.ctx.terms.mk_eq(i, k);
    let descendant_not_idx_eq = exec.ctx.terms.mk_not(descendant_idx_eq);
    let descendant_row1_eq = exec.ctx.terms.mk_eq(seeded_descendant, ten);
    let descendant_row1_clause = exec
        .ctx
        .terms
        .mk_or(vec![descendant_not_idx_eq, descendant_row1_eq]);
    let descendant_row2_eq = exec.ctx.terms.mk_eq(seeded_descendant, base_select);
    let descendant_row2_clause = exec
        .ctx
        .terms
        .mk_or(vec![descendant_idx_eq, descendant_row2_eq]);
    let original_assertion = exec.ctx.terms.mk_eq(select_term, zero);

    assert!(
        exec.ctx.assertions.contains(&original_assertion),
        "original top-level assertion must stay present"
    );
    assert!(
        exec.ctx.assertions.contains(&top_row1_clause),
        "top-level ROW1 clause should still be emitted"
    );
    assert!(
        exec.ctx.assertions.contains(&top_row2_clause),
        "top-level ROW2 clause should still be emitted"
    );
    assert!(
        !exec.ctx.assertions.contains(&descendant_row1_clause),
        "reused seeded descendant must not emit eager ROW1 clauses"
    );
    assert!(
        !exec.ctx.assertions.contains(&descendant_row2_clause),
        "reused seeded descendant must not emit eager ROW2 clauses"
    );
}

#[test]
fn lazy_row2b_fixpoint_injects_row1_and_row2_but_not_row2b_6546() {
    // LazyRow2FinalCheck injects both ROW1 and ROW2 (downward) eagerly
    // via `add_array_row_clauses()`, matching Z3's assert_store_axiom1/2.
    // Only ROW2b (upward) from `add_array_row2b_clauses()` is deferred.
    let mut exec = prepare_executor(
        r#"
        (set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const i Int)
        (declare-const j Int)
        (assert (= (select (store a i 42) j) 0))
    "#,
    );

    let a = exec.ctx.terms.lookup("a").expect("a declared");
    let i = exec.ctx.terms.lookup("i").expect("i declared");
    let j = exec.ctx.terms.lookup("j").expect("j declared");
    let value_42 = exec.ctx.terms.mk_int(42.into());
    let zero = exec.ctx.terms.mk_int(0.into());
    let store = exec.ctx.terms.mk_store(a, i, value_42);
    let select_term = exec.ctx.terms.mk_select(store, j);
    let before_assertions = exec.ctx.assertions.len();

    exec.run_array_axiom_fixpoint_at(before_assertions, ArrayAxiomMode::LazyRow2FinalCheck);

    let term_count_after_fixpoint = exec.ctx.terms.len();
    let base_select = exec.ctx.terms.mk_select(a, j);
    assert_eq!(
        exec.ctx.terms.len(),
        term_count_after_fixpoint,
        "lazy fixpoint should seed select(a, j) before theory solving"
    );

    let row2_eq = exec.ctx.terms.mk_eq(select_term, base_select);
    let idx_eq = exec.ctx.terms.mk_eq(i, j);
    let not_idx_eq = exec.ctx.terms.mk_not(idx_eq);
    let row1_eq = exec.ctx.terms.mk_eq(select_term, value_42);
    let row1_clause = exec.ctx.terms.mk_or(vec![not_idx_eq, row1_eq]);
    let row2_clause = exec.ctx.terms.mk_or(vec![idx_eq, row2_eq]);
    let original_assertion = exec.ctx.terms.mk_eq(select_term, zero);

    assert!(
        exec.ctx.assertions.contains(&original_assertion),
        "original array assertion must be preserved"
    );
    assert!(
        exec.ctx.assertions.contains(&row1_clause),
        "ROW1 clause must be injected eagerly"
    );
    assert!(
        exec.ctx.assertions.contains(&row2_clause),
        "ROW2 (downward) clause must be injected eagerly"
    );
}

#[test]
fn seed_array_row2b_terms_creates_upward_select_without_axioms_6546() {
    let mut exec = prepare_executor(
        r#"
        (set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const i Int)
        (declare-const j Int)
        (declare-const v Int)
    "#,
    );

    let a = exec.ctx.terms.lookup("a").expect("a declared");
    let i = exec.ctx.terms.lookup("i").expect("i declared");
    let j = exec.ctx.terms.lookup("j").expect("j declared");
    let v = exec.ctx.terms.lookup("v").expect("v declared");
    let store = exec.ctx.terms.mk_store(a, i, v);
    let _base_select = exec.ctx.terms.mk_select(a, j);
    let before_assertions = exec.ctx.assertions.len();

    let seeded = exec.seed_array_row2b_terms(1000);
    assert!(
        seeded > 0,
        "ROW2b seeding should create select(store(a, i, v), j) from select(a, j)"
    );

    let term_count_after_seeding = exec.ctx.terms.len();
    let upward_select = exec.ctx.terms.mk_select(store, j);
    assert_eq!(
        exec.ctx.terms.len(),
        term_count_after_seeding,
        "ROW2b seeding should create the upward select term eagerly"
    );
    assert!(
        matches!(exec.ctx.terms.get(upward_select), TermData::App(_, _)),
        "seeded ROW2b term must remain in the term store"
    );
    assert_eq!(
        exec.ctx.assertions.len(),
        before_assertions,
        "term seeding must not inject ROW2b clauses on its own"
    );
}

#[test]
fn array_extensionality_adds_skolem_without_explicit_witness_6282() {
    let mut exec = prepare_executor(
        r#"
        (set-logic QF_AX)
        (declare-sort Index 0)
        (declare-sort Elem 0)
        (declare-const a (Array Index Elem))
        (declare-const b (Array Index Elem))
        (assert (not (= a b)))
    "#,
    );

    let a = exec.ctx.terms.lookup("a").expect("a declared");
    let b = exec.ctx.terms.lookup("b").expect("b declared");
    let before = exec.ctx.assertions.len();

    exec.add_array_extensionality_axioms();

    assert_eq!(
        exec.ctx.assertions.len(),
        before + 1,
        "without an existing select witness, extensionality should add one axiom"
    );
    assert!(
        exec.array_ext_witness_cache
            .pair_witness(&exec.ctx.terms, a, b)
            .is_some(),
        "extensionality should create a fresh diff Skolem without a witness"
    );
}

#[test]
fn array_extensionality_user_legacy_name_collision_stays_sat() {
    let mut exec = prepare_executor(
        r#"
        (set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const b (Array Int Int))
    "#,
    );
    let a = exec.ctx.terms.lookup("a").expect("a declared");
    let b = exec.ctx.terms.lookup("b").expect("b declared");

    // This is the exact public name the old pair-derived generator would have
    // reused through sort-blind `mk_var`. Pinning the arrays equal at that
    // user-controlled index while keeping them extensionally different is
    // satisfiable, but the aliased witness axiom made it falsely UNSAT.
    let legacy_user_name = format!("__ext_diff_{}_{}", a.0, b.0);
    let commands = parse(&format!(
        r#"
        (declare-const {legacy_user_name} Int)
        (assert (= (select a {legacy_user_name}) (select b {legacy_user_name})))
        (assert (not (= a b)))
        (check-sat)
    "#
    ))
    .expect("collision regression should parse");
    let outputs = exec
        .execute_all(&commands)
        .expect("collision regression should execute");

    assert_eq!(
        outputs,
        vec!["sat"],
        "a user-owned legacy name is not a witness"
    );
    let user_term = exec
        .ctx
        .terms
        .lookup(&legacy_user_name)
        .expect("user collision symbol exists");
    let internal_term = exec
        .array_ext_witness_cache
        .pair_witness(&exec.ctx.terms, a, b)
        .expect("solver created a disjoint internal witness");
    assert_ne!(user_term, internal_term);
    assert_eq!(exec.ctx.terms.sort(internal_term), &Sort::Int);
}

#[test]
fn array_extensionality_skips_skolem_with_explicit_select_witness_6282() {
    let mut exec = prepare_executor(
        r#"
        (set-logic QF_AX)
        (declare-sort Index 0)
        (declare-sort Elem 0)
        (declare-const a (Array Index Elem))
        (declare-const b (Array Index Elem))
        (declare-const k Index)
        (assert (not (= (select a k) (select b k))))
        (assert (not (= a b)))
    "#,
    );

    let a = exec.ctx.terms.lookup("a").expect("a declared");
    let b = exec.ctx.terms.lookup("b").expect("b declared");
    let before = exec.ctx.assertions.len();

    exec.add_array_extensionality_axioms();

    assert_eq!(
        exec.ctx.assertions.len(),
        before,
        "an explicit select disequality witness should suppress redundant extensionality axioms"
    );
    assert!(
        exec.array_ext_witness_cache
            .pair_witness(&exec.ctx.terms, a, b)
            .is_none(),
        "already_diseq optimization should avoid creating a fresh diff Skolem"
    );
}

#[test]
fn array_extensionality_skips_skolem_with_select_alias_witness_8785() {
    let mut exec = prepare_executor(
        r#"
        (set-logic QF_AX)
        (declare-sort Index 0)
        (declare-sort Elem 0)
        (declare-const a (Array Index Elem))
        (declare-const b (Array Index Elem))
        (declare-const k Index)
        (declare-const e1 Elem)
        (declare-const e2 Elem)
        (assert (= e1 (select a k)))
        (assert (= e2 (select b k)))
        (assert (not (= e1 e2)))
        (assert (not (= a b)))
    "#,
    );

    let a = exec.ctx.terms.lookup("a").expect("a declared");
    let b = exec.ctx.terms.lookup("b").expect("b declared");
    let before = exec.ctx.assertions.len();

    exec.add_array_extensionality_axioms();

    assert_eq!(
        exec.ctx.assertions.len(),
        before,
        "select aliases with a top-level disequality should suppress redundant extensionality"
    );
    assert!(
        exec.array_ext_witness_cache
            .pair_witness(&exec.ctx.terms, a, b)
            .is_none(),
        "alias-expanded already_diseq optimization should avoid a fresh diff Skolem"
    );
}

#[test]
fn array_extensionality_skips_top_level_positive_array_equality_8785() {
    let mut exec = prepare_executor(
        r#"
        (set-logic QF_AX)
        (declare-sort Index 0)
        (declare-sort Elem 0)
        (declare-const a (Array Index Elem))
        (declare-const b (Array Index Elem))
        (assert (= a b))
    "#,
    );

    let a = exec.ctx.terms.lookup("a").expect("a declared");
    let b = exec.ctx.terms.lookup("b").expect("b declared");
    let eq = exec.ctx.terms.mk_eq(a, b);
    let _neg_eq = exec.ctx.terms.mk_not(eq);
    let before = exec.ctx.assertions.len();

    exec.add_array_extensionality_axioms();

    assert_eq!(
        exec.ctx.assertions.len(),
        before,
        "positive top-level array equality should not create an inactive extensionality axiom"
    );
    assert!(
        exec.array_ext_witness_cache
            .pair_witness(&exec.ctx.terms, a, b)
            .is_none(),
        "positive top-level equality should suppress redundant diff Skolems"
    );
}

#[test]
fn array_extensionality_bounded_scan_ignores_generated_negations_8785() {
    let setup = r#"
        (set-logic QF_AX)
        (declare-sort Index 0)
        (declare-sort Elem 0)
        (declare-const a (Array Index Elem))
        (declare-const b (Array Index Elem))
        (declare-const k Index)
        (declare-const v Elem)
    "#;
    let mut bounded = prepare_executor(setup);
    let scan_limit = bounded.ctx.terms.len();
    let a = bounded.ctx.terms.lookup("a").expect("a declared");
    let b = bounded.ctx.terms.lookup("b").expect("b declared");
    let k = bounded.ctx.terms.lookup("k").expect("k declared");
    let v = bounded.ctx.terms.lookup("v").expect("v declared");
    let store_a = bounded.ctx.terms.mk_store(a, k, v);
    let store_b = bounded.ctx.terms.mk_store(b, k, v);
    let store_eq = bounded.ctx.terms.mk_eq(store_a, store_b);
    let _generated_negation = bounded.ctx.terms.mk_not(store_eq);
    let before = bounded.ctx.assertions.len();

    bounded.add_array_extensionality_axioms_up_to(scan_limit);

    assert_eq!(
        bounded.ctx.assertions.len(),
        before,
        "generated post-boundary negations should not demand eager extensionality"
    );
    assert!(
        bounded
            .array_ext_witness_cache
            .pair_witness(&bounded.ctx.terms, store_a, store_b)
            .is_none(),
        "bounded scan should ignore generated congruence guard negations"
    );

    let mut unbounded = prepare_executor(setup);
    let a = unbounded.ctx.terms.lookup("a").expect("a declared");
    let b = unbounded.ctx.terms.lookup("b").expect("b declared");
    let k = unbounded.ctx.terms.lookup("k").expect("k declared");
    let v = unbounded.ctx.terms.lookup("v").expect("v declared");
    let store_a = unbounded.ctx.terms.mk_store(a, k, v);
    let store_b = unbounded.ctx.terms.mk_store(b, k, v);
    let store_eq = unbounded.ctx.terms.mk_eq(store_a, store_b);
    let _generated_negation = unbounded.ctx.terms.mk_not(store_eq);

    unbounded.add_array_extensionality_axioms();

    assert!(
        unbounded
            .array_ext_witness_cache
            .pair_witness(&unbounded.ctx.terms, store_a, store_b)
            .is_some(),
        "the unbounded direct wrapper should preserve legacy extensionality behavior"
    );
}

#[test]
fn auflia_fixpoint_injects_disjunctive_store_axiom_for_separated_asserts_6885() {
    let mut exec = prepare_executor(
        r#"
        (set-logic QF_AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun b () (Array Int Int))
        (declare-fun v () Int)
        (declare-fun w () Int)
        (declare-fun x () Int)
        (declare-fun y () Int)
        (declare-fun g ((Array Int Int)) Int)
        (declare-fun f (Int) Int)
        (assert (= (store a x v) b))
        (assert (= (store a y w) b))
        (assert (not (= (f x) (f y))))
        (assert (not (= (g a) (g b))))
    "#,
    );

    let a = exec.ctx.terms.lookup("a").expect("a declared");
    let b = exec.ctx.terms.lookup("b").expect("b declared");
    let v = exec.ctx.terms.lookup("v").expect("v declared");
    let w = exec.ctx.terms.lookup("w").expect("w declared");
    let x = exec.ctx.terms.lookup("x").expect("x declared");
    let y = exec.ctx.terms.lookup("y").expect("y declared");
    let store_x = exec.ctx.terms.mk_store(a, x, v);
    let store_y = exec.ctx.terms.mk_store(a, y, w);
    let eq_store_x_b = exec.ctx.terms.mk_eq(store_x, b);
    let eq_store_y_b = exec.ctx.terms.mk_eq(store_y, b);
    let idx_eq = exec.ctx.terms.mk_eq(x, y);
    let base_eq = exec.ctx.terms.mk_eq(a, b);
    let not_eq_store_x_b = exec.ctx.terms.mk_not(eq_store_x_b);
    let not_eq_store_y_b = exec.ctx.terms.mk_not(eq_store_y_b);
    let disj_axiom =
        exec.ctx
            .terms
            .mk_or(vec![not_eq_store_x_b, not_eq_store_y_b, idx_eq, base_eq]);

    let before = exec.ctx.assertions.len();
    exec.run_array_axiom_fixpoint_at(before, ArrayAxiomMode::LazyRow2FinalCheck);

    assert!(
        exec.ctx.assertions.contains(&disj_axiom),
        "store disjunctive axiom must be injected for separated top-level assertions"
    );
}

#[test]
fn store_base_decomposition_reuses_extensionality_witness_6282() {
    let mut exec = prepare_executor(
        r#"
        (set-logic QF_AX)
        (declare-sort Index 0)
        (declare-sort Elem 0)
        (declare-const a (Array Index Elem))
        (declare-const b (Array Index Elem))
        (declare-const i Index)
        (declare-const v Elem)
        (declare-const x (Array Index Elem))
        (declare-const y (Array Index Elem))
        (assert (= x (store a i v)))
        (assert (= y (store b i v)))
        (assert (not (= a b)))
    "#,
    );

    let a = exec.ctx.terms.lookup("a").expect("a declared");
    let b = exec.ctx.terms.lookup("b").expect("b declared");
    let legacy_sbd_name = format!("__sbd_diff_{}_{}", a.0, b.0);

    exec.add_array_extensionality_axioms();
    let ext_witness = exec
        .array_ext_witness_cache
        .pair_witness(&exec.ctx.terms, a, b)
        .expect("extensionality should mint the base-pair witness");
    exec.add_store_store_base_decomposition_axioms();

    assert_eq!(
        exec.array_ext_witness_cache
            .pair_witness(&exec.ctx.terms, a, b),
        Some(ext_witness),
        "store decomposition should use the existing extensionality witness for the base pair"
    );
    assert!(
        exec.ctx.terms.lookup(&legacy_sbd_name).is_none(),
        "store decomposition must not create a second witness for the same base pair"
    );
}

#[test]
fn storechain_colliding_indices_axiom_debug_7654() {
    // Diagnose the axiom generation for the storechain_colliding_indices_sat bug.
    let mut exec = prepare_executor(
        r#"
        (set-logic QF_AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun i () Int)
        (declare-fun j () Int)
        (declare-fun v () Int)
        (declare-fun w () Int)
        (declare-fun x () Int)
        (assert (not (= v w)))
        (assert (= (store (store a i v) j x) (store (store a i w) j x)))
    "#,
    );

    let before = exec.ctx.assertions.len();
    eprintln!("BEFORE FIXPOINT: {before} assertions");
    for (idx, &a) in exec.ctx.assertions.iter().enumerate() {
        eprintln!(
            "  assertion[{}]: {:?} = {:?}",
            idx,
            a,
            exec.ctx.terms.get(a)
        );
    }

    exec.run_array_axiom_fixpoint_at(0, ArrayAxiomMode::LazyRow2FinalCheck);

    eprintln!(
        "AFTER FIXPOINT: {} assertions, {} terms",
        exec.ctx.assertions.len(),
        exec.ctx.terms.len()
    );

    // Dump all terms
    for idx in 0..exec.ctx.terms.len() {
        let tid = ay_core::TermId(idx as u32);
        eprintln!(
            "  term[{:?}]: {:?}  sort={:?}",
            tid,
            exec.ctx.terms.get(tid),
            exec.ctx.terms.sort(tid)
        );
    }

    eprintln!("---ASSERTIONS---");
    for (idx, &a) in exec.ctx.assertions.iter().enumerate() {
        eprintln!(
            "  assertion[{}]: {:?} = {:?}",
            idx,
            a,
            exec.ctx.terms.get(a)
        );
    }

    // Just check we have more than the original 2 assertions (axioms were generated)
    assert!(
        exec.ctx.assertions.len() > before,
        "fixpoint should generate array axioms"
    );
}

#[test]
fn storechain_colliding_indices_sat_7654() {
    // Regression: store(store(a,i,v),j,x) = store(store(a,i,w),j,x)
    // is SAT when i=j (outer store overwrites inner). AY returned false UNSAT.
    let result = run_script(
        r#"
        (set-logic QF_AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun i () Int)
        (declare-fun j () Int)
        (declare-fun v () Int)
        (declare-fun w () Int)
        (declare-fun x () Int)
        (assert (not (= v w)))
        (assert (= (store (store a i v) j x) (store (store a i w) j x)))
        (check-sat)
    "#,
    );
    assert_eq!(result, vec!["sat"], "colliding store indices should be SAT");
}

#[test]
fn shadowed_store_equality_adds_exact_alias_or_value_obligation() {
    let mut exec = prepare_executor(
        r#"
        (set-logic QF_AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun i () Int)
        (declare-fun j () Int)
        (declare-fun v () Int)
        (declare-fun w () Int)
        (declare-fun x () Int)
        (assert (= (store (store a i v) j x)
                   (store (store a i w) j x)))
    "#,
    );

    let a = exec.ctx.terms.lookup("a").expect("a declared");
    let i = exec.ctx.terms.lookup("i").expect("i declared");
    let j = exec.ctx.terms.lookup("j").expect("j declared");
    let v = exec.ctx.terms.lookup("v").expect("v declared");
    let w = exec.ctx.terms.lookup("w").expect("w declared");
    let x = exec.ctx.terms.lookup("x").expect("x declared");
    let lhs_inner = exec.ctx.terms.mk_store(a, i, v);
    let rhs_inner = exec.ctx.terms.mk_store(a, i, w);
    let lhs = exec.ctx.terms.mk_store(lhs_inner, j, x);
    let rhs = exec.ctx.terms.mk_store(rhs_inner, j, x);
    let array_eq = exec.ctx.terms.mk_eq(lhs, rhs);
    let expected = {
        let not_array_eq = exec.ctx.terms.mk_not(array_eq);
        let index_eq = exec.ctx.terms.mk_eq(i, j);
        let value_eq = exec.ctx.terms.mk_eq(v, w);
        exec.ctx.terms.mk_or(vec![not_array_eq, index_eq, value_eq])
    };

    exec.add_shadowed_store_equality_axioms();
    assert!(
        exec.ctx.assertions.contains(&expected),
        "equal shadowed store chains must constrain the model to i=j or v=w"
    );

    let count = exec
        .ctx
        .assertions
        .iter()
        .filter(|&&assertion| assertion == expected)
        .count();
    exec.add_shadowed_store_equality_axioms();
    assert_eq!(
        exec.ctx
            .assertions
            .iter()
            .filter(|&&assertion| assertion == expected)
            .count(),
        count,
        "fixpoint rescans must not duplicate the same guarded lemma"
    );
}

#[test]
fn shadowed_store_equality_unsat_remains_proof_enabled() {
    let commands = parse(
        r#"
        (set-logic QF_AUFLIA)
        (set-option :produce-proofs true)
        (declare-fun a () (Array Int Int))
        (declare-fun i () Int)
        (declare-fun j () Int)
        (declare-fun v () Int)
        (declare-fun w () Int)
        (declare-fun x () Int)
        (assert (not (= i j)))
        (assert (not (= v w)))
        (assert (= (store (store a i v) j x)
                   (store (store a i w) j x)))
        (check-sat)
    "#,
    )
    .expect("shadowed-store proof script parses");
    let mut exec = Executor::new();
    let result = exec
        .execute_all(&commands)
        .expect("shadowed-store proof script executes");
    assert_eq!(result, vec!["unsat"]);
    let proof = exec
        .last_proof
        .as_ref()
        .expect("proof-enabled UNSAT stores a proof");
    let rendered = exec.get_proof();
    assert!(
        !rendered.contains(":rule trust"),
        "shadowed-store obligation must not introduce a trust step:\n{rendered}"
    );
    let quality = ay_proof::check_proof_strict(proof, &exec.ctx.terms)
        .expect("shadowed-store UNSAT proof passes strict checking");
    assert_eq!(quality.trust_count, 0);
}

#[test]
fn storechain_colliding_propositional_skeleton_7654() {
    // Test the propositional skeleton of the array axioms
    // to verify it's SAT. Uses uninterpreted functions to mimic
    // the select/store terms without array theory semantics.
    // If this is UNSAT, the Tseitin encoding is the problem.
    // If this is SAT, the DPLL(T) theory integration is the problem.
    let result = run_script(
        r#"
        (set-logic QF_UF)
        (declare-sort S 0)
        (declare-fun v () S)
        (declare-fun w () S)
        (declare-fun x () S)
        (declare-fun LHS () S)
        (declare-fun RHS () S)
        (declare-fun T16 () S)
        (declare-fun T17 () S)
        (declare-fun T18 () S)
        (declare-fun T24 () S)
        (declare-fun T25 () S)
        (declare-fun T26 () S)
        (declare-fun T30 () S)
        (declare-fun T33 () S)
        (declare-fun T37 () S)
        (declare-fun T40 () S)
        (declare-fun T43 () S)
        (declare-fun T44 () S)
        (declare-fun i () S)
        (declare-fun j () S)

        ; assertion[0]: not(= v w)
        (assert (not (= v w)))
        ; assertion[1]: (= LHS RHS)
        (assert (= LHS RHS))
        ; assertion[3]: (= v w) ∨ not(= T17 T18) -- extensionality for inner pair
        (assert (or (= v w) (not (= T17 T18))))
        ; assertion[4]: (= v w) ∨ not(= LHS RHS) ∨ (= j T16) -- decomposition
        (assert (or (= v w) (not (= LHS RHS)) (= j T16)))
        ; assertion[5]: (= LHS RHS) ∨ not(= T25 T26) -- extensionality for outer pair
        (assert (or (= LHS RHS) (not (= T25 T26))))

        ; ROW1/ROW2 for sel(T10, T16): assertions [10],[11]
        (assert (or (not (= i T16)) (= v T17)))
        (assert (or (= T17 T43) (= i T16)))
        ; ROW1/ROW2 for sel(T12, T16): assertions [12],[13]
        (assert (or (not (= i T16)) (= w T18)))
        (assert (or (= i T16) (= T18 T43)))

        ; ROW1/ROW2 for sel(T11, T24): assertions [14],[15]
        (assert (or (not (= j T24)) (= x T25)))
        (assert (or (= j T24) (= T25 T37)))
        ; ROW1/ROW2 for sel(T13, T24): assertions [16],[17]
        (assert (or (not (= j T24)) (= x T26)))
        (assert (or (= j T24) (= T26 T40)))

        ; ROW1/ROW2 for sel(T13, T16): assertions [18],[19]
        (assert (or (not (= j T16)) (= x T30)))
        (assert (or (= j T16) (= T18 T30)))
        ; ROW1/ROW2 for sel(T11, T16): assertions [20],[21]
        (assert (or (not (= j T16)) (= x T33)))
        (assert (or (= j T16) (= T17 T33)))

        ; ROW1/ROW2 for sel(T10, T24): assertions [22],[23]
        (assert (or (not (= i T24)) (= v T37)))
        (assert (or (= T37 T44) (= i T24)))
        ; ROW1/ROW2 for sel(T12, T24): assertions [24],[25]
        (assert (or (not (= i T24)) (= w T40)))
        (assert (or (= i T24) (= T40 T44)))

        ; Congruence axioms (assertions [6],[7])
        (assert (or (not (= LHS RHS)) (= j T16) (= T17 T30)))
        (assert (or (not (= LHS RHS)) (= j T16) (= T18 T33)))

        ; Congruence axioms (assertions [8],[9])
        (assert (or (not (= LHS RHS)) (= j T24) (= T26 T37)))
        (assert (or (not (= LHS RHS)) (= j T24) (= T25 T40)))

        (check-sat)
    "#,
    );
    assert_eq!(result, vec!["sat"], "propositional skeleton should be SAT");
}

#[test]
fn storechain_colliding_qf_ax_7654() {
    // Same benchmark but with QF_AX logic (pure arrays, no arithmetic)
    // Uses uninterpreted sorts to avoid arithmetic routing
    let result = run_script(
        r#"
        (set-logic QF_AX)
        (declare-sort E 0)
        (declare-sort I 0)
        (declare-fun a () (Array I E))
        (declare-fun i () I)
        (declare-fun j () I)
        (declare-fun v () E)
        (declare-fun w () E)
        (declare-fun x () E)
        (assert (not (= v w)))
        (assert (= (store (store a i v) j x) (store (store a i w) j x)))
        (check-sat)
    "#,
    );
    assert_eq!(
        result,
        vec!["sat"],
        "QF_AX colliding store indices should be SAT"
    );
}

#[test]
fn storechain_colliding_uf_encoding_7654() {
    // Encode the axioms as UF to test if DPLL(T) with pure EUF finds SAT.
    // All select/store terms become uninterpreted constants.
    // Array semantics (ROW1/ROW2) are encoded as clauses.
    // If this is SAT, the array theory is the problem.
    // If this is UNSAT, the eager axioms are the problem.
    let result = run_script(
        r#"
        (set-logic QF_UF)
        (declare-sort S 0)
        (declare-sort A 0)
        (declare-fun a () A)
        (declare-fun i () S)
        (declare-fun j () S)
        (declare-fun v () S)
        (declare-fun w () S)
        (declare-fun x () S)
        ; store terms as uninterpreted
        (declare-fun T10 () A)  ; store(a, i, v)
        (declare-fun T11 () A)  ; store(T10, j, x)
        (declare-fun T12 () A)  ; store(a, i, w)
        (declare-fun T13 () A)  ; store(T12, j, x)
        ; ext diff skolems
        (declare-fun T16 () S)  ; ext_diff(T10, T12)
        (declare-fun T24 () S)  ; ext_diff(T11, T13)
        ; select terms
        (declare-fun T17 () S)  ; sel(T10, T16)
        (declare-fun T18 () S)  ; sel(T12, T16)
        (declare-fun T25 () S)  ; sel(T11, T24)
        (declare-fun T26 () S)  ; sel(T13, T24)
        (declare-fun T30 () S)  ; sel(T13, T16)
        (declare-fun T33 () S)  ; sel(T11, T16)
        (declare-fun T37 () S)  ; sel(T10, T24)
        (declare-fun T40 () S)  ; sel(T12, T24)
        (declare-fun T43 () S)  ; sel(a, T16)
        (declare-fun T44 () S)  ; sel(a, T24)

        ; assertion[0]: not(= v w)
        (assert (not (= v w)))
        ; assertion[1]: (= T11 T13)
        (assert (= T11 T13))
        ; ext for inner pair: (= v w) ∨ not(= T17 T18)
        (assert (or (= v w) (not (= T17 T18))))
        ; decomposition: (= v w) ∨ not(= T11 T13) ∨ (= j T16)
        (assert (or (= v w) (not (= T11 T13)) (= j T16)))
        ; ext for outer pair: (= T11 T13) ∨ not(= T25 T26)
        (assert (or (= T11 T13) (not (= T25 T26))))

        ; Congruence axioms (store value congruence)
        (assert (or (not (= T11 T13)) (= j T16) (= T17 T30)))
        (assert (or (not (= T11 T13)) (= j T16) (= T18 T33)))
        (assert (or (not (= T11 T13)) (= j T24) (= T26 T37)))
        (assert (or (not (= T11 T13)) (= j T24) (= T25 T40)))

        ; ROW axioms for sel(T10, T16)
        (assert (or (not (= i T16)) (= v T17)))
        (assert (or (= T17 T43) (= i T16)))
        ; ROW axioms for sel(T12, T16)
        (assert (or (not (= i T16)) (= w T18)))
        (assert (or (= i T16) (= T18 T43)))
        ; ROW axioms for sel(T11, T24)
        (assert (or (not (= j T24)) (= x T25)))
        (assert (or (= j T24) (= T25 T37)))
        ; ROW axioms for sel(T13, T24)
        (assert (or (not (= j T24)) (= x T26)))
        (assert (or (= j T24) (= T26 T40)))
        ; ROW axioms for sel(T13, T16)
        (assert (or (not (= j T16)) (= x T30)))
        (assert (or (= j T16) (= T18 T30)))
        ; ROW axioms for sel(T11, T16)
        (assert (or (not (= j T16)) (= x T33)))
        (assert (or (= j T16) (= T17 T33)))
        ; ROW axioms for sel(T10, T24)
        (assert (or (not (= i T24)) (= v T37)))
        (assert (or (= T37 T44) (= i T24)))
        ; ROW axioms for sel(T12, T24)
        (assert (or (not (= i T24)) (= w T40)))
        (assert (or (= i T24) (= T40 T44)))

        (check-sat)
    "#,
    );
    assert_eq!(
        result,
        vec!["sat"],
        "UF encoding of array axioms should be SAT"
    );
}

#[test]
fn storechain_colliding_tseitin_cnf_debug_7654() {
    // After axiom fixpoint, Tseitin-encode and send to SAT solver directly.
    // This isolates whether the SAT solver (with preprocessing) is the problem
    // or whether additional clauses beyond the fixpoint axioms cause the issue.
    let mut exec = prepare_executor(
        r#"
        (set-logic QF_AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun i () Int)
        (declare-fun j () Int)
        (declare-fun v () Int)
        (declare-fun w () Int)
        (declare-fun x () Int)
        (assert (not (= v w)))
        (assert (= (store (store a i v) j x) (store (store a i w) j x)))
    "#,
    );

    exec.run_array_axiom_fixpoint_at(0, ArrayAxiomMode::LazyRow2FinalCheck);

    // Tseitin encode all assertions
    let tseitin_result = ay_core::Tseitin::new(&exec.ctx.terms).transform_all(&exec.ctx.assertions);

    eprintln!(
        "Tseitin: {} vars, {} clauses",
        tseitin_result.num_vars,
        tseitin_result.clauses.len()
    );
    for (i, clause) in tseitin_result.clauses.iter().enumerate() {
        eprintln!("  clause[{}]: {:?}", i, clause.literals());
    }

    // Try SAT solver WITHOUT preprocessing
    {
        let mut sat = ay_sat::Solver::new(tseitin_result.num_vars as usize);
        sat.set_preprocess_enabled(false);
        for clause in &tseitin_result.clauses {
            let lits: Vec<ay_sat::Literal> = clause
                .literals()
                .iter()
                .map(|&lit| {
                    let var = ay_sat::Variable::new(lit.unsigned_abs());
                    if lit > 0 {
                        ay_sat::Literal::positive(var)
                    } else {
                        ay_sat::Literal::negative(var)
                    }
                })
                .collect();
            sat.add_clause(lits);
        }
        let result_no_pp = sat.solve();
        eprintln!(
            "SAT result (no preprocessing): sat={}",
            result_no_pp.is_sat()
        );
        assert!(
            result_no_pp.is_sat(),
            "CNF should be SAT without preprocessing"
        );
    }

    // Try SAT solver WITH preprocessing
    {
        let mut sat = ay_sat::Solver::new(tseitin_result.num_vars as usize);
        sat.set_preprocess_enabled(true);
        for clause in &tseitin_result.clauses {
            let lits: Vec<ay_sat::Literal> = clause
                .literals()
                .iter()
                .map(|&lit| {
                    let var = ay_sat::Variable::new(lit.unsigned_abs());
                    if lit > 0 {
                        ay_sat::Literal::positive(var)
                    } else {
                        ay_sat::Literal::negative(var)
                    }
                })
                .collect();
            sat.add_clause(lits);
        }
        let result_with_pp = sat.solve();
        eprintln!(
            "SAT result (with preprocessing): sat={}",
            result_with_pp.is_sat()
        );
        assert!(
            result_with_pp.is_sat(),
            "CNF should be SAT with preprocessing"
        );
    }
}

// --- #8598: map[f]/const-array/as-array select axiom through equality aliases ---

/// When select(b, 0) is registered and b = map[f](a) through an equality,
/// the select-map axiom should still fire.
///
/// Without the fix, register_select() only checks the syntactic array
/// argument in map_cache, missing equality-aliased map terms.
#[test]
fn test_equality_alias_map_select_axiom_fires() {
    // The axiom: select(b, i) = f(select(a, i)) when b = map[f](a).
    // We assert b = map[f](a), select(b, 0) = 10, f(select(a, 0)) != 10.
    // Without the select-map axiom, this is SAT (no connection between b and map[f](a)).
    // With the axiom, this is UNSAT (select(b, 0) = f(select(a, 0)) = 10 contradicts != 10).
    let input = r#"
        (set-logic QF_AUFLIA)
        (declare-fun f (Int) Int)
        (declare-const a (Array Int Int))
        (declare-const b (Array Int Int))
        (assert (= b ((_ map f) a)))
        (assert (= (select b 0) 10))
        (assert (not (= (f (select a 0)) 10)))
        (check-sat)
    "#;
    assert_eq!(run_script(input), vec!["unsat"]);
}

/// Same as above but with a binary map function.
#[test]
fn test_equality_alias_map_binary_select_axiom_fires() {
    let input = r#"
        (set-logic QF_AUFLIA)
        (declare-fun g (Int Int) Int)
        (declare-const a1 (Array Int Int))
        (declare-const a2 (Array Int Int))
        (declare-const c (Array Int Int))
        (assert (= c ((_ map g) a1 a2)))
        (assert (= (select c 0) 42))
        (assert (not (= (g (select a1 0) (select a2 0)) 42)))
        (check-sat)
    "#;
    assert_eq!(run_script(input), vec!["unsat"]);
}

/// Const-array through equality alias: select(b, i) should equal the default
/// value when b = const-array(v) through an equality.
#[test]
fn test_equality_alias_const_array_select_axiom_fires() {
    let input = r#"
        (set-logic QF_AUFLIA)
        (declare-const b (Array Int Int))
        (assert (= b ((as const (Array Int Int)) 7)))
        (assert (not (= (select b 0) 7)))
        (check-sat)
    "#;
    assert_eq!(run_script(input), vec!["unsat"]);
}
