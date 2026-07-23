// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

use super::lemmas::{
    apply_theory_lemma_incremental, apply_theory_lemma_incremental_persistent,
    take_new_theory_lemmas,
};
use super::{
    add_extra_blocking_clauses, bias_split_clause_vars, encode_and_add_split_clause,
    encode_split_pair_incremental, ensure_incremental_atom_encoded,
    map_conflict_to_blocking_clause, replay_incremental_bound_refinements, BlockingClauseResult,
    BoundRefinementReplayKey,
};
use crate::incremental_proof_cache::{IncrementalNegationCache, TheoryLemmaSeenSet};
// #8529: Use deterministic hash sets in all builds.
use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::{BoundRefinementRequest, Sort, TermStore, TheoryConflict, TheoryLemma, TheoryLit};
use ay_sat::{Literal as SatLiteral, SatResult, Solver as SatSolver, Variable as SatVariable};
use num_bigint::BigInt;
use num_rational::BigRational;

struct DuplicateReplayCheckpoint {
    clauses: usize,
    terms: usize,
    next_var: u32,
    mapping_len: usize,
}

fn assert_duplicate_refinement_replay_state(
    solver: &SatSolver,
    terms: &TermStore,
    local_next_var: u32,
    local_term_to_var_len: usize,
    checkpoint: &DuplicateReplayCheckpoint,
    added_refinement_clauses: &HashSet<BoundRefinementReplayKey>,
) {
    assert_eq!(
        solver.num_clauses(),
        checkpoint.clauses,
        "duplicate refinement replay should not add the same implication twice"
    );
    assert_eq!(
        terms.len(),
        checkpoint.terms,
        "duplicate refinement replay should skip term materialization"
    );
    assert_eq!(
        local_next_var, checkpoint.next_var,
        "duplicate refinement replay should not allocate fresh SAT vars"
    );
    assert_eq!(
        local_term_to_var_len, checkpoint.mapping_len,
        "duplicate refinement replay should not grow atom mappings"
    );
    assert_eq!(
        added_refinement_clauses.len(),
        1,
        "duplicate refinement replay should keep one normalized key"
    );
}

#[test]
fn encode_split_pair_incremental_reuses_existing_split_atoms_issue_6586() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let lt_atom = terms.mk_lt(x, y);
    let gt_atom = terms.mk_gt(x, y);

    let mut solver = SatSolver::new(0);
    let mut local_term_to_var = super::HashMap::default();
    let mut local_var_to_term = super::HashMap::default();
    let mut local_next_var = 0;
    let mut negations = IncrementalNegationCache::seed(&mut terms, std::iter::empty(), false);

    let first = encode_split_pair_incremental(
        &terms,
        &mut solver,
        &mut local_term_to_var,
        &mut local_var_to_term,
        &mut local_next_var,
        &mut negations,
        (lt_atom, gt_atom),
    )
    .expect("first split encoding should succeed");
    let vars_after_first = solver.user_num_vars();
    let next_var_after_first = local_next_var;
    let term_count_after_first = local_term_to_var.len();
    let reverse_count_after_first = local_var_to_term.len();

    let second = encode_split_pair_incremental(
        &terms,
        &mut solver,
        &mut local_term_to_var,
        &mut local_var_to_term,
        &mut local_next_var,
        &mut negations,
        (lt_atom, gt_atom),
    )
    .expect("re-encoding the same split should reuse SAT vars");

    assert_eq!(second, first, "split roots should keep stable SAT vars");
    assert_eq!(
        solver.user_num_vars(),
        vars_after_first,
        "reusing split atoms must not allocate fresh SAT vars"
    );
    assert_eq!(
        local_next_var, next_var_after_first,
        "reusing split atoms must not advance the SAT var cursor"
    );
    assert_eq!(
        local_term_to_var.len(),
        term_count_after_first,
        "reusing split atoms must not grow the forward map"
    );
    assert_eq!(
        local_var_to_term.len(),
        reverse_count_after_first,
        "reusing split atoms must not grow the reverse map"
    );
}

#[test]
fn encode_and_add_split_clause_skips_duplicate_clause_issue_6586() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let lt_atom = terms.mk_lt(x, y);
    let gt_atom = terms.mk_gt(x, y);

    let mut solver = SatSolver::new(0);
    let mut local_term_to_var = super::HashMap::default();
    let mut local_var_to_term = super::HashMap::default();
    let mut local_next_var = 0;
    let mut added_split_clauses = HashSet::default();
    let mut negations = IncrementalNegationCache::seed(&mut terms, std::iter::empty(), false);

    let (first_left, first_right, first_added) = encode_and_add_split_clause(
        &terms,
        &mut solver,
        &mut local_term_to_var,
        &mut local_var_to_term,
        &mut local_next_var,
        &mut negations,
        lt_atom,
        gt_atom,
        None,
        &mut added_split_clauses,
    );
    assert!(first_added, "first split encoding should add SAT clauses");
    let clauses_after_first = solver.num_clauses();

    let (second_left, second_right, second_added) = encode_and_add_split_clause(
        &terms,
        &mut solver,
        &mut local_term_to_var,
        &mut local_var_to_term,
        &mut local_next_var,
        &mut negations,
        lt_atom,
        gt_atom,
        None,
        &mut added_split_clauses,
    );

    assert_eq!(
        (second_left, second_right),
        (first_left, first_right),
        "duplicate split should reuse SAT vars"
    );
    assert!(
        !second_added,
        "duplicate split should report that no fresh clauses were added"
    );
    assert_eq!(
        solver.num_clauses(),
        clauses_after_first,
        "duplicate split should not add another identical clause"
    );
    assert_eq!(
        added_split_clauses.len(),
        1,
        "duplicate split should keep only one clause key"
    );
}

#[test]
fn encode_and_add_split_clause_blocks_cached_assignment_issue_8785() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let q = terms.mk_var("q", Sort::Bool);

    let mut solver = SatSolver::new(0);
    let mut local_term_to_var = super::HashMap::default();
    let mut local_var_to_term = super::HashMap::default();
    let mut local_next_var = 0;
    let mut added_split_clauses = HashSet::default();
    let mut negations = IncrementalNegationCache::seed(&mut terms, std::iter::empty(), false);

    let p_var = ensure_incremental_atom_encoded(
        &terms,
        &mut solver,
        &mut local_term_to_var,
        &mut local_var_to_term,
        &mut local_next_var,
        &mut negations,
        p,
    );
    let q_var = ensure_incremental_atom_encoded(
        &terms,
        &mut solver,
        &mut local_term_to_var,
        &mut local_var_to_term,
        &mut local_next_var,
        &mut negations,
        q,
    );

    solver.push();
    solver.add_clause(vec![SatLiteral::negative(p_var)]);
    solver.add_clause(vec![SatLiteral::negative(q_var)]);
    assert!(matches!(solver.solve().into_inner(), SatResult::Sat(_)));

    let (_, _, added) = encode_and_add_split_clause(
        &terms,
        &mut solver,
        &mut local_term_to_var,
        &mut local_var_to_term,
        &mut local_next_var,
        &mut negations,
        p,
        q,
        None,
        &mut added_split_clauses,
    );
    assert!(added, "fresh split should be inserted as a live SAT lemma");
    assert!(
        solver.solve().into_inner().is_unsat(),
        "split clause (p v q) should immediately block the cached ¬p/¬q model"
    );

    assert!(solver.pop());
    assert!(
        matches!(solver.solve().into_inner(), SatResult::Sat(_)),
        "split clause should not survive its assertion scope"
    );
}

#[test]
fn encode_and_add_split_clause_negates_not_wrapped_disequality_guard_9604() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let minus_one = terms.mk_int(BigInt::from(-1));
    let one = terms.mk_int(BigInt::from(1));
    let eq_zero = terms.mk_eq(x, zero);
    let not_eq_zero = terms.mk_not(eq_zero);
    let le = terms.mk_le(x, minus_one);
    let ge = terms.mk_ge(x, one);

    let mut solver = SatSolver::new(0);
    let mut local_term_to_var = super::HashMap::default();
    let mut local_var_to_term = super::HashMap::default();
    let mut local_next_var = 0;
    let mut added_split_clauses = HashSet::default();
    let mut negations = IncrementalNegationCache::seed(&mut terms, std::iter::empty(), false);

    let not_eq_var = ensure_incremental_atom_encoded(
        &terms,
        &mut solver,
        &mut local_term_to_var,
        &mut local_var_to_term,
        &mut local_next_var,
        &mut negations,
        not_eq_zero,
    );
    let (le_var, ge_var, added) = encode_and_add_split_clause(
        &terms,
        &mut solver,
        &mut local_term_to_var,
        &mut local_var_to_term,
        &mut local_next_var,
        &mut negations,
        le,
        ge,
        Some((not_eq_zero, false)),
        &mut added_split_clauses,
    );

    assert!(
        added,
        "fresh not-wrapped disequality split should add clauses"
    );
    solver.add_clause(vec![SatLiteral::positive(not_eq_var)]);
    solver.add_clause(vec![SatLiteral::negative(le_var)]);
    solver.add_clause(vec![SatLiteral::negative(ge_var)]);
    assert!(
        solver.solve().into_inner().is_unsat(),
        "not-wrapped disequality guard must force one split branch when the disequality holds"
    );
}

#[test]
fn map_conflict_to_blocking_clause_blocks_cached_assignment_issue_8785() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let q = terms.mk_var("q", Sort::Bool);

    let mut solver = SatSolver::new(0);
    let mut local_term_to_var = super::HashMap::default();
    let mut local_var_to_term = super::HashMap::default();
    let mut local_next_var = 0;
    let mut negations = IncrementalNegationCache::seed(&mut terms, std::iter::empty(), false);

    let p_var = ensure_incremental_atom_encoded(
        &terms,
        &mut solver,
        &mut local_term_to_var,
        &mut local_var_to_term,
        &mut local_next_var,
        &mut negations,
        p,
    );
    let q_var = ensure_incremental_atom_encoded(
        &terms,
        &mut solver,
        &mut local_term_to_var,
        &mut local_var_to_term,
        &mut local_next_var,
        &mut negations,
        q,
    );

    solver.push();
    solver.add_clause(vec![SatLiteral::positive(p_var)]);
    solver.add_clause(vec![SatLiteral::negative(q_var)]);
    assert!(matches!(solver.solve().into_inner(), SatResult::Sat(_)));

    let result = map_conflict_to_blocking_clause(
        &mut solver,
        &[TheoryLit::new(p, true), TheoryLit::new(q, false)],
        &[],
        &local_term_to_var,
    );
    assert!(matches!(result, BlockingClauseResult::Added));
    assert!(
        solver.solve().into_inner().is_unsat(),
        "blocking clause (not p v q) should immediately invalidate the current p/not-q model"
    );

    assert!(solver.pop());
    assert!(
        matches!(solver.solve().into_inner(), SatResult::Sat(_)),
        "blocking clause should not survive its assertion scope"
    );
}

#[test]
fn extra_bound_conflict_batch_preserves_every_pending_clause() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let q = terms.mk_var("q", Sort::Bool);
    let r = terms.mk_var("r", Sort::Bool);

    let mut local_term_to_var = super::HashMap::default();
    local_term_to_var.insert(p, 0);
    local_term_to_var.insert(q, 1);
    local_term_to_var.insert(r, 2);

    let p_var = SatVariable::new(0);
    let q_var = SatVariable::new(1);
    let r_var = SatVariable::new(2);
    let mut solver = SatSolver::new(3);
    solver.set_preprocess_enabled(false);

    // Force q and r opposite p without creating root-level units. A complete
    // model therefore leaves all three variables assigned above level zero,
    // matching the incremental theory-batch path that exposed the overwrite.
    solver.add_clause(vec![
        SatLiteral::positive(p_var),
        SatLiteral::positive(q_var),
    ]);
    solver.add_clause(vec![
        SatLiteral::negative(p_var),
        SatLiteral::negative(q_var),
    ]);
    solver.add_clause(vec![
        SatLiteral::positive(p_var),
        SatLiteral::positive(r_var),
    ]);
    solver.add_clause(vec![
        SatLiteral::negative(p_var),
        SatLiteral::negative(r_var),
    ]);

    let model = match solver.solve().into_inner() {
        SatResult::Sat(model) => model,
        other => panic!("opposite-polarity fixture must be SAT, got {other:?}"),
    };
    let conflicts = [
        TheoryConflict::new(vec![
            TheoryLit::new(p, model[0]),
            TheoryLit::new(q, model[1]),
        ]),
        TheoryConflict::new(vec![
            TheoryLit::new(p, model[0]),
            TheoryLit::new(r, model[2]),
        ]),
    ];

    add_extra_blocking_clauses(&mut solver, &conflicts, &local_term_to_var);

    let first = solver
        .take_pending_theory_conflict()
        .expect("first all-false extra conflict must remain pending");
    let second = solver
        .take_pending_theory_conflict()
        .expect("second all-false extra conflict must not overwrite the first");
    assert_ne!(first, second);
    assert_eq!(solver.take_pending_theory_conflict(), None);
}

#[test]
fn replay_incremental_bound_refinements_skips_duplicate_clause_issue_6586() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let zero = terms.mk_rational(BigRational::from(BigInt::from(0)));
    let trigger_atom = terms.mk_ge(x, zero);

    let mut solver = SatSolver::new(0);
    let mut local_term_to_var = super::HashMap::default();
    let mut local_var_to_term = super::HashMap::default();
    let mut local_next_var = 0;
    let mut added_refinement_clauses = HashSet::default();
    let mut negations = IncrementalNegationCache::seed(&mut terms, std::iter::empty(), false);

    let trigger_var = ensure_incremental_atom_encoded(
        &terms,
        &mut solver,
        &mut local_term_to_var,
        &mut local_var_to_term,
        &mut local_next_var,
        &mut negations,
        trigger_atom,
    );
    solver.add_clause(vec![SatLiteral::positive(trigger_var)]);

    let request = BoundRefinementRequest {
        variable: x,
        rhs_term: None,
        bound_value: BigRational::from(BigInt::from(1)),
        is_upper: true,
        is_integer: false,
        reason: vec![TheoryLit::new(trigger_atom, true)],
    };

    assert!(replay_incremental_bound_refinements(
        &mut terms,
        &mut solver,
        &mut local_term_to_var,
        &mut local_var_to_term,
        &mut local_next_var,
        &mut negations,
        std::slice::from_ref(&request),
        &mut added_refinement_clauses,
    ));
    let checkpoint = DuplicateReplayCheckpoint {
        clauses: solver.num_clauses(),
        terms: terms.len(),
        next_var: local_next_var,
        mapping_len: local_term_to_var.len(),
    };

    assert!(replay_incremental_bound_refinements(
        &mut terms,
        &mut solver,
        &mut local_term_to_var,
        &mut local_var_to_term,
        &mut local_next_var,
        &mut negations,
        &[request],
        &mut added_refinement_clauses,
    ));

    assert_duplicate_refinement_replay_state(
        &solver,
        &terms,
        local_next_var,
        local_term_to_var.len(),
        &checkpoint,
        &added_refinement_clauses,
    );
}

#[test]
fn bound_refinement_replay_key_normalizes_integer_bounds_and_reason_order_issue_6586() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Bool);
    let z = terms.mk_var("z", Sort::Bool);

    let first = BoundRefinementReplayKey::new(&BoundRefinementRequest {
        variable: x,
        rhs_term: None,
        bound_value: BigRational::new(BigInt::from(7), BigInt::from(2)),
        is_upper: true,
        is_integer: true,
        reason: vec![TheoryLit::new(z, false), TheoryLit::new(y, true)],
    });
    let second = BoundRefinementReplayKey::new(&BoundRefinementRequest {
        variable: x,
        rhs_term: None,
        bound_value: BigRational::new(BigInt::from(3), BigInt::from(1)),
        is_upper: true,
        is_integer: true,
        reason: vec![
            TheoryLit::new(y, true),
            TheoryLit::new(z, false),
            TheoryLit::new(y, true),
        ],
    });

    assert_eq!(
        first, second,
        "request-level replay keys should canonicalize integer bounds and reason literals"
    );
}

#[test]
fn bias_split_clause_vars_prefers_canonical_left_branch_issue_8785() {
    let mut solver = SatSolver::new(2);
    let left_var = SatVariable::new(0);
    let right_var = SatVariable::new(1);

    bias_split_clause_vars(&mut solver, left_var, right_var);

    assert_eq!(
        solver.var_phase(left_var),
        Some(true),
        "disequality/expression split left branch should be tried as true"
    );
    assert_eq!(
        solver.var_phase(right_var),
        Some(false),
        "disequality/expression split right branch should remain available but not be the default"
    );
}

#[test]
fn take_new_theory_lemmas_filters_canonical_duplicates_issue_8785() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let q = terms.mk_var("q", Sort::Bool);
    let r = terms.mk_var("r", Sort::Bool);

    let first = TheoryLemma::new(vec![TheoryLit::new(p, true), TheoryLit::new(q, false)]);
    let reordered = TheoryLemma::new(vec![TheoryLit::new(q, false), TheoryLit::new(p, true)]);
    let different_reason = TheoryLemma::new(vec![TheoryLit::new(p, true), TheoryLit::new(r, true)]);

    let mut seen = TheoryLemmaSeenSet::default();
    let (new_lemmas, skipped) = take_new_theory_lemmas(
        vec![first.clone(), reordered, different_reason.clone()],
        &mut seen,
    );

    assert_eq!(skipped, 1, "reordered duplicate clause should be skipped");
    assert_eq!(
        new_lemmas,
        vec![first.clone(), different_reason.clone()],
        "first occurrences should keep their original order"
    );

    let (new_lemmas, skipped) = take_new_theory_lemmas(vec![first, different_reason], &mut seen);
    assert!(
        new_lemmas.is_empty(),
        "already applied theory lemmas should not be replayed"
    );
    assert_eq!(skipped, 2);
}

#[test]
fn apply_theory_lemma_incremental_encodes_fresh_atoms_issue_6662() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let q = terms.mk_var("q", Sort::Bool);

    let mut solver = SatSolver::new(0);
    let mut local_term_to_var = super::HashMap::default();
    let mut local_var_to_term = super::HashMap::default();
    let mut local_next_var = 0;
    let mut negations = IncrementalNegationCache::seed(&mut terms, std::iter::empty(), false);

    apply_theory_lemma_incremental(
        &terms,
        &mut solver,
        &mut local_term_to_var,
        &mut local_var_to_term,
        &mut local_next_var,
        &mut negations,
        &[TheoryLit::new(p, true), TheoryLit::new(q, false)],
    );

    let p_var = ensure_incremental_atom_encoded(
        &terms,
        &mut solver,
        &mut local_term_to_var,
        &mut local_var_to_term,
        &mut local_next_var,
        &mut negations,
        p,
    );
    let q_var = ensure_incremental_atom_encoded(
        &terms,
        &mut solver,
        &mut local_term_to_var,
        &mut local_var_to_term,
        &mut local_next_var,
        &mut negations,
        q,
    );
    solver.add_clause(vec![SatLiteral::negative(p_var)]);
    solver.add_clause(vec![SatLiteral::positive(q_var)]);

    assert!(
        solver.solve().into_inner().is_unsat(),
        "lemma (p ∨ ¬q) plus ¬p and q should be UNSAT after on-demand encoding"
    );
}

#[test]
fn apply_theory_lemma_incremental_blocks_cached_assignment_issue_8785() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let q = terms.mk_var("q", Sort::Bool);

    let mut solver = SatSolver::new(0);
    let mut local_term_to_var = super::HashMap::default();
    let mut local_var_to_term = super::HashMap::default();
    let mut local_next_var = 0;
    let mut negations = IncrementalNegationCache::seed(&mut terms, std::iter::empty(), false);

    let p_var = ensure_incremental_atom_encoded(
        &terms,
        &mut solver,
        &mut local_term_to_var,
        &mut local_var_to_term,
        &mut local_next_var,
        &mut negations,
        p,
    );
    let q_var = ensure_incremental_atom_encoded(
        &terms,
        &mut solver,
        &mut local_term_to_var,
        &mut local_var_to_term,
        &mut local_next_var,
        &mut negations,
        q,
    );

    solver.push();
    solver.add_clause(vec![SatLiteral::negative(p_var)]);
    solver.add_clause(vec![SatLiteral::positive(q_var)]);
    assert!(matches!(solver.solve().into_inner(), SatResult::Sat(_)));

    apply_theory_lemma_incremental(
        &terms,
        &mut solver,
        &mut local_term_to_var,
        &mut local_var_to_term,
        &mut local_next_var,
        &mut negations,
        &[TheoryLit::new(p, true), TheoryLit::new(q, false)],
    );
    assert!(
        solver.solve().into_inner().is_unsat(),
        "lemma (p ∨ ¬q) should immediately invalidate the current ¬p/q model"
    );

    assert!(solver.pop());
    assert!(
        matches!(solver.solve().into_inner(), SatResult::Sat(_)),
        "incremental theory lemma should not survive its assertion scope"
    );
}

#[test]
fn apply_theory_lemma_incremental_persistent_respects_scope_issue_6719() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);

    let mut solver = SatSolver::new(0);
    solver.enable_clause_trace();
    let mut term_to_var = super::HashMap::default();
    let mut var_to_term = super::HashMap::default();
    let mut negations = IncrementalNegationCache::seed(&mut terms, std::iter::empty(), false);

    solver.push();
    let recorded = apply_theory_lemma_incremental_persistent(
        &mut solver,
        &mut term_to_var,
        &mut var_to_term,
        &mut negations,
        &[TheoryLit::new(p, true)],
    );
    assert!(
        recorded,
        "unit theory lemma should be retained in the SAT original-clause ledger"
    );
    assert_eq!(
        solver
            .clause_trace()
            .expect("clause trace enabled")
            .original_clauses()
            .count(),
        1,
        "scoped no-split lemma should appear once in the trace"
    );

    let mut local_next_var = 0;
    let p_var = ensure_incremental_atom_encoded(
        &terms,
        &mut solver,
        &mut term_to_var,
        &mut var_to_term,
        &mut local_next_var,
        &mut negations,
        p,
    );
    solver.add_clause_global(vec![SatLiteral::negative(p_var)]);
    assert!(
        solver.solve().into_inner().is_unsat(),
        "scoped lemma p together with global ¬p should be UNSAT before pop"
    );

    assert!(
        solver.pop(),
        "expected scoped lemma push frame to pop cleanly"
    );
    assert!(
        matches!(solver.solve().into_inner(), SatResult::Sat(_)),
        "no-split theory lemma must be scoped, not global, after pop"
    );
}

#[test]
fn apply_theory_lemma_incremental_persistent_skips_tautology_trace_issue_6719() {
    let mut terms = TermStore::new();
    let q = terms.mk_var("q", Sort::Bool);

    let mut solver = SatSolver::new(0);
    solver.enable_clause_trace();
    let mut term_to_var = super::HashMap::default();
    let mut var_to_term = super::HashMap::default();
    let mut negations = IncrementalNegationCache::seed(&mut terms, std::iter::empty(), false);

    let trace_original_count = solver
        .clause_trace()
        .expect("clause trace enabled")
        .original_clauses()
        .count();
    let tautology_recorded = apply_theory_lemma_incremental_persistent(
        &mut solver,
        &mut term_to_var,
        &mut var_to_term,
        &mut negations,
        &[TheoryLit::new(q, true), TheoryLit::new(q, false)],
    );
    assert!(
        !tautology_recorded,
        "tautological theory lemmas must not claim a SAT original-clause slot"
    );
    assert_eq!(
        solver
            .clause_trace()
            .expect("clause trace enabled")
            .original_clauses()
            .count(),
        trace_original_count,
        "tautological no-split lemma must not grow the clause trace"
    );
}

#[test]
fn ensure_incremental_atom_encoded_preserves_not_polarity_from_eq_coerce_issue_8738() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let eq_false = terms.mk_eq_coerce(x, terms.false_term());
    assert!(
        matches!(terms.get(eq_false), ay_core::TermData::Not(inner) if *inner == x),
        "mk_eq_coerce(x, false) should simplify to Not(x) for this regression"
    );

    let mut solver = SatSolver::new(0);
    let mut local_term_to_var = super::HashMap::default();
    let mut local_var_to_term = super::HashMap::default();
    let mut local_next_var = 0;
    let mut negations = IncrementalNegationCache::seed(&mut terms, std::iter::empty(), false);

    let not_x_var = ensure_incremental_atom_encoded(
        &terms,
        &mut solver,
        &mut local_term_to_var,
        &mut local_var_to_term,
        &mut local_next_var,
        &mut negations,
        eq_false,
    );
    let x_var = ensure_incremental_atom_encoded(
        &terms,
        &mut solver,
        &mut local_term_to_var,
        &mut local_var_to_term,
        &mut local_next_var,
        &mut negations,
        x,
    );

    assert_ne!(
        not_x_var, x_var,
        "negative-root fallback must allocate a distinct adapter var instead of aliasing x"
    );
    solver.add_clause(vec![SatLiteral::positive(not_x_var)]);
    solver.add_clause(vec![SatLiteral::positive(x_var)]);

    assert!(
        solver.solve().into_inner().is_unsat(),
        "asserting Not(x) and x must be UNSAT; returned var must preserve atom polarity"
    );
}

#[test]
fn ensure_incremental_atom_encoded_not_atom_remains_sat_when_consistent_issue_8738() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let eq_false = terms.mk_eq_coerce(x, terms.false_term());

    let mut solver = SatSolver::new(0);
    let mut local_term_to_var = super::HashMap::default();
    let mut local_var_to_term = super::HashMap::default();
    let mut local_next_var = 0;
    let mut negations = IncrementalNegationCache::seed(&mut terms, std::iter::empty(), false);

    let not_x_var = ensure_incremental_atom_encoded(
        &terms,
        &mut solver,
        &mut local_term_to_var,
        &mut local_var_to_term,
        &mut local_next_var,
        &mut negations,
        eq_false,
    );
    let x_var = ensure_incremental_atom_encoded(
        &terms,
        &mut solver,
        &mut local_term_to_var,
        &mut local_var_to_term,
        &mut local_next_var,
        &mut negations,
        x,
    );

    solver.add_clause(vec![SatLiteral::positive(not_x_var)]);
    solver.add_clause(vec![SatLiteral::negative(x_var)]);

    assert!(
        matches!(solver.solve().into_inner(), SatResult::Sat(_)),
        "asserting Not(x) together with x=false must remain SAT"
    );
}

#[test]
fn ensure_incremental_atom_encoded_keeps_positive_root_fallback_behavior_issue_8738() {
    let mut terms = TermStore::new();
    let false_term = terms.false_term();

    let mut solver = SatSolver::new(0);
    let mut local_term_to_var = super::HashMap::default();
    let mut local_var_to_term = super::HashMap::default();
    let mut local_next_var = 0;
    let mut negations = IncrementalNegationCache::seed(&mut terms, std::iter::empty(), false);

    let false_var = ensure_incremental_atom_encoded(
        &terms,
        &mut solver,
        &mut local_term_to_var,
        &mut local_var_to_term,
        &mut local_next_var,
        &mut negations,
        false_term,
    );

    assert_eq!(
        local_next_var, 1,
        "positive-root fallback must keep the existing direct alias path"
    );
    assert_eq!(
        local_term_to_var.get(&false_term).copied(),
        Some(false_var.index() as u32),
        "false constant should map directly to the Tseitin root var"
    );

    solver.add_clause(vec![SatLiteral::positive(false_var)]);
    assert!(
        solver.solve().into_inner().is_unsat(),
        "asserting the false constant as true must remain UNSAT"
    );
}
