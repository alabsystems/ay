// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Tests for the goal-to-goal tactics framework (`tactics.rs`).
//!
//! Coverage:
//! - HONESTY GATE: the backing `flatten-and` pass reports `true` only when it
//!   actually flattens, and `false` on a goal with nothing to flatten (both
//!   directions).
//! - Combinator semantics for `then` / `or-else`.
//! - DIFFERENTIAL/EQUIVALENCE: ~10 nested-AND formulas (sat and unsat) solved
//!   WITH and WITHOUT the tactic produce identical SAT/UNSAT verdicts.

use super::*;
use crate::api::{Logic, Solver, Sort, Term};
use ay_core::{TermData, TermId, TermStore};
use ay_frontend::{ApplyTactic, Probe, ProbeCmp};

// ---------------------------------------------------------------------------
// HONESTY GATE: backing pass reports progress truthfully (both directions).
// ---------------------------------------------------------------------------

#[test]
fn tactic_flatten_and_reports_progress_when_it_flattens() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let c = terms.mk_var("c", Sort::Bool);
    // (and (and a b) c)
    let inner = terms.mk_and(vec![a, b]);
    let outer = terms.mk_and(vec![inner, c]);

    let mut goal = vec![outer];
    let progressed = Tactic::flatten_and().apply(&mut terms, &mut goal);

    assert!(
        progressed,
        "flatten-and must report progress when it flattens"
    );
    assert_eq!(goal.len(), 3, "nested AND should flatten to 3 conjuncts");
    assert!(goal.contains(&a));
    assert!(goal.contains(&b));
    assert!(goal.contains(&c));
}

#[test]
fn tactic_flatten_and_reports_no_progress_when_nothing_to_flatten() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    // Two atoms, no AND to flatten.
    let mut goal = vec![a, b];
    let progressed = Tactic::flatten_and().apply(&mut terms, &mut goal);

    assert!(
        !progressed,
        "flatten-and must report NO progress when there is nothing to flatten"
    );
    assert_eq!(goal, vec![a, b], "identity goal must be left unchanged");
}

// ---------------------------------------------------------------------------
// Combinator semantics.
// ---------------------------------------------------------------------------

#[test]
fn tactic_then_progress_if_either_branch_progresses() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let inner = terms.mk_and(vec![a, b]);

    // First flatten-and flattens; the second runs on the already-flat goal
    // (no progress) but `then` still reports overall progress.
    let mut goal = vec![inner];
    let t = Tactic::flatten_and().then(Tactic::flatten_and());
    let progressed = t.apply(&mut terms, &mut goal);
    assert!(progressed);
    assert_eq!(goal.len(), 2);
    assert!(goal.contains(&a));
    assert!(goal.contains(&b));
}

#[test]
fn tactic_then_no_progress_when_neither_branch_progresses() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let mut goal = vec![a, b];
    let t = Tactic::flatten_and().then(Tactic::flatten_and());
    assert!(!t.apply(&mut terms, &mut goal));
    assert_eq!(goal, vec![a, b]);
}

#[test]
fn tactic_or_else_takes_first_when_it_progresses() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let inner = terms.mk_and(vec![a, b]);
    let mut goal = vec![inner];

    // First branch flattens -> overall progress, second branch never runs.
    let t = Tactic::flatten_and().or_else(Tactic::flatten_and());
    assert!(t.apply(&mut terms, &mut goal));
    assert_eq!(goal.len(), 2);
}

#[test]
fn tactic_or_else_falls_back_and_restores_goal_when_first_no_progress() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    // Already flat: first branch makes no progress, fallback also no progress,
    // and the goal must be left exactly as it was.
    let mut goal = vec![a, b];
    let t = Tactic::flatten_and().or_else(Tactic::flatten_and());
    assert!(!t.apply(&mut terms, &mut goal));
    assert_eq!(goal, vec![a, b]);
}

#[test]
fn tactic_names_are_stable() {
    assert_eq!(Tactic::flatten_and().name(), "flatten-and");
    assert_eq!(
        Tactic::flatten_and().then(Tactic::flatten_and()).name(),
        "(then flatten-and flatten-and)"
    );
    assert_eq!(
        Tactic::flatten_and().or_else(Tactic::flatten_and()).name(),
        "(or-else flatten-and flatten-and)"
    );
    assert_eq!(Tactic::Fail.name(), "fail");
    assert_eq!(Tactic::SplitClause.name(), "split-clause");
    assert_eq!(
        Tactic::flatten_and().repeat().name(),
        "(repeat flatten-and)"
    );
    assert_eq!(
        Tactic::flatten_and().repeat_up_to(3).name(),
        "(repeat flatten-and 3)"
    );
}

// ---------------------------------------------------------------------------
// New combinators / multi-subgoal engine (A-I3).
// ---------------------------------------------------------------------------

/// A depth-0 root goal over `formulas`.
fn root(formulas: Vec<ay_core::TermId>) -> Goal {
    Goal::root(formulas)
}

#[test]
fn fail_tactic_is_an_honest_failure() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let err = Tactic::Fail
        .apply_goals(&mut terms, root(vec![a]))
        .expect_err("fail must fail");
    assert_eq!(err.message, "fail tactic");
}

#[test]
fn or_else_falls_through_on_failure_only() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let inner = terms.mk_and(vec![a, b]);
    // (or-else fail flatten-and): fail fails, so flatten-and runs on the original.
    let t = Tactic::Fail.or_else(Tactic::flatten_and());
    let goals = t.apply_goals(&mut terms, root(vec![inner])).expect("ok");
    assert_eq!(goals.len(), 1);
    assert_eq!(goals[0].formulas.len(), 2, "flatten-and fallback ran");
    assert_eq!(goals[0].depth, 1);
}

#[test]
fn or_else_keeps_first_success_even_without_progress() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    // (or-else skip fail): skip SUCCEEDS (no failure), so `fail` never runs.
    let t = Tactic::Skip.or_else(Tactic::Fail);
    let goals = t.apply_goals(&mut terms, root(vec![a])).expect("skip wins");
    assert_eq!(goals.len(), 1);
    assert_eq!(goals[0].depth, 0, "skip is depth 0 and fail did not run");
}

#[test]
fn split_clause_produces_one_goal_per_disjunct() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let c = terms.mk_var("c", Sort::Bool);
    let clause = terms.mk_or(vec![a, b]);
    // goal: {(or a b), c}
    let goals = Tactic::SplitClause
        .apply_goals(&mut terms, root(vec![clause, c]))
        .expect("has a clause");
    assert_eq!(goals.len(), 2, "two disjuncts -> two goals");
    // Each subgoal keeps the other assertion `c` and replaces the clause with a
    // single disjunct; depth is 1.
    assert!(goals.iter().all(|g| g.depth == 1));
    assert!(goals.iter().all(|g| g.formulas.contains(&c)));
    assert!(goals.iter().any(|g| g.formulas.contains(&a)));
    assert!(goals.iter().any(|g| g.formulas.contains(&b)));
    assert!(goals.iter().all(|g| !g.formulas.contains(&clause)));
}

#[test]
fn split_clause_without_a_clause_fails() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let err = Tactic::SplitClause
        .apply_goals(&mut terms, root(vec![a]))
        .expect_err("no clause -> fail");
    assert!(
        err.message.contains("does not contain any clause"),
        "got: {}",
        err.message
    );
}

#[test]
fn repeat_counts_the_fixpoint_confirmation_application() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let c = terms.mk_var("c", Sort::Bool);
    let inner = terms.mk_and(vec![a, b]);
    let outer = terms.mk_and(vec![inner, c]);
    // Here the goal is fed UNflattened (a single `and` formula), bypassing the
    // construction-time flatten that the real `(apply)` surface performs. So
    // (repeat elim-and) takes TWO applications: the first flattens to {a,b,c}
    // (depth 1), the second confirms the fixpoint and makes no further progress
    // (depth 2). Z3 counts every applied primitive, so the confirming
    // application's increment is kept — byte-confirmed vs z3 4.x, where
    // `(then elim-and elim-and)` on a flat goal is depth 2. (On the real apply
    // surface the goal is pre-flattened at construction, so `(repeat elim-and)`
    // there is depth 1: a single confirming application.)
    let goals = Tactic::flatten_and()
        .repeat()
        .apply_goals(&mut terms, root(vec![outer]))
        .expect("ok");
    assert_eq!(goals.len(), 1);
    assert_eq!(goals[0].formulas.len(), 3);
    assert_eq!(
        goals[0].depth, 2,
        "the fixpoint-confirming application counts"
    );
}

#[test]
fn repeat_on_a_flat_goal_counts_the_single_confirming_application() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    // Already flat (as goals are on the real apply surface): the body makes no
    // structural progress on the first run, so repeat stops — but that single
    // application still ran, so its depth increment counts (depth 1). It never
    // loops forever. Byte-confirmed vs z3 4.x:
    //   (assert a)(assert b)(apply (repeat elim-and)) -> :depth 1
    let goals = Tactic::flatten_and()
        .repeat()
        .apply_goals(&mut terms, root(vec![a, b]))
        .expect("ok");
    assert_eq!(goals.len(), 1);
    assert_eq!(goals[0].depth, 1);
    assert_eq!(goals[0].formulas, vec![a, b]);
}

#[test]
fn when_gates_on_the_probe() {
    let mut terms = TermStore::new();
    // Use NON-Boolean constants: Z3's `num-consts` excludes Bool-sorted
    // constants, so a conjunction of Int equalities has num-consts = 3.
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let z = terms.mk_var("z", Sort::Int);
    let e1 = terms.mk_eq(x, y);
    let e2 = terms.mk_eq(y, z);
    let inner = terms.mk_and(vec![e1, e2]);
    let gt0 = Probe::Cmp(
        ProbeCmp::Gt,
        Box::new(Probe::NumConsts),
        Box::new(Probe::Const("0".to_string())),
    );
    // Probe holds (num-consts = 3 > 0) -> flatten-and runs.
    let held = Tactic::When(gt0.clone(), Box::new(Tactic::flatten_and()));
    let goals = held.apply_goals(&mut terms, root(vec![inner])).expect("ok");
    assert_eq!(goals[0].formulas.len(), 2);
    assert_eq!(goals[0].depth, 1);

    // Probe fails (num-consts > 100 is false) -> skip, depth unchanged.
    let gt100 = Probe::Cmp(
        ProbeCmp::Gt,
        Box::new(Probe::NumConsts),
        Box::new(Probe::Const("100".to_string())),
    );
    let inner2 = terms.mk_and(vec![e1, e2]);
    let skipped = Tactic::When(gt100, Box::new(Tactic::flatten_and()));
    let goals = skipped
        .apply_goals(&mut terms, root(vec![inner2]))
        .expect("ok");
    assert_eq!(goals[0].formulas, vec![inner2], "skipped: unchanged");
    assert_eq!(goals[0].depth, 0);
}

#[test]
fn fail_if_fails_only_when_the_probe_holds() {
    let mut terms = TermStore::new();
    // A non-Boolean (Int) equality: num-consts = 2 (Z3 counts x, y).
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let eq = terms.mk_eq(x, y);
    let has_consts = Probe::Cmp(
        ProbeCmp::Gt,
        Box::new(Probe::NumConsts),
        Box::new(Probe::Const("0".to_string())),
    );
    assert!(Tactic::FailIf(has_consts)
        .apply_goals(&mut terms, root(vec![eq]))
        .is_err());

    let no_consts = Probe::Cmp(
        ProbeCmp::Gt,
        Box::new(Probe::Size),
        Box::new(Probe::Const("100".to_string())),
    );
    let goals = Tactic::FailIf(no_consts)
        .apply_goals(&mut terms, root(vec![eq]))
        .expect("probe false -> skip");
    assert_eq!(goals[0].depth, 0);
}

#[test]
fn cond_picks_the_branch_the_probe_selects() {
    let mut terms = TermStore::new();
    // (and (and a b) c) — a nested-AND Bool goal.
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let c = terms.mk_var("c", Sort::Bool);
    let inner = terms.mk_and(vec![a, b]);
    let outer = terms.mk_and(vec![inner, c]);

    // `size` after Z3 top-level-and splitting is 1 for the single nested AND
    // (the outer `and` is one formula; splitting happens in the probe evaluator
    // which flattens it to 3). Use an is-propositional probe (true here) to pick.
    let is_prop = Probe::IsPropositional;

    // probe TRUE -> branch t1 (flatten-and) runs: 3 conjuncts, depth 1.
    let t = Tactic::cond(is_prop.clone(), Tactic::flatten_and(), Tactic::Fail);
    let goals = t.apply_goals(&mut terms, root(vec![outer])).expect("ok");
    assert_eq!(goals[0].formulas.len(), 3, "true branch flattened");
    assert_eq!(goals[0].depth, 1);

    // probe FALSE -> branch t2 runs. Here t2 = flatten-and, t1 = fail; with an
    // Int goal is-propositional is false, so t2 (flatten-and) runs, NOT fail.
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let z = terms.mk_var("z", Sort::Int);
    let e1 = terms.mk_eq(x, y);
    let e2 = terms.mk_eq(y, z);
    let inner_i = terms.mk_and(vec![e1, e2]);
    let t2 = Tactic::cond(Probe::IsPropositional, Tactic::Fail, Tactic::flatten_and());
    let goals = t2
        .apply_goals(&mut terms, root(vec![inner_i]))
        .expect("false branch is flatten-and, not fail");
    assert_eq!(goals[0].formulas.len(), 2, "false branch flattened the AND");
}

#[test]
fn cond_propagates_a_chosen_branch_failure_without_fallthrough() {
    // Z3's `cond(p, fail, skip)` with `p` TRUE genuinely FAILS — it must NOT
    // silently fall through to the `skip` else-branch (that is the whole reason
    // `Cond` is a primitive, not `(or-else (when p t1) t2)`).
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let t = Tactic::cond(Probe::IsPropositional, Tactic::Fail, Tactic::Skip);
    assert!(
        t.apply_goals(&mut terms, root(vec![a])).is_err(),
        "true-probe cond must propagate the chosen fail branch"
    );
}

#[test]
fn fail_if_not_decided_is_identity_only_on_a_decided_goal() {
    let mut terms = TermStore::new();

    // Empty goal ⇒ decided SAT ⇒ identity (depth unchanged).
    let goals = Tactic::fail_if_not_decided()
        .apply_goals(&mut terms, root(vec![]))
        .expect("empty goal is decided-sat");
    assert_eq!(goals.len(), 1);
    assert!(goals[0].formulas.is_empty());
    assert_eq!(goals[0].depth, 0);

    // Goal containing `false` ⇒ decided UNSAT ⇒ identity.
    let ff = terms.mk_bool(false);
    let goals = Tactic::fail_if_not_decided()
        .apply_goals(&mut terms, root(vec![ff]))
        .expect("false goal is decided-unsat");
    assert_eq!(goals[0].formulas, vec![ff]);
    assert_eq!(goals[0].depth, 0);

    // A non-trivial goal is NOT decided ⇒ honest failure.
    let x = terms.mk_var("x", Sort::Bool);
    assert!(
        Tactic::fail_if_not_decided()
            .apply_goals(&mut terms, root(vec![x]))
            .is_err(),
        "an undecided goal must fail fail-if-not-decided"
    );
}

// ---------------------------------------------------------------------------
// PROBE Z3-PARITY: probe VALUES match Z3 4.15.4's goal model exactly.
//
// The expected numbers below were captured from `z3 -smt2` (4.15.4) via
// `(apply (when (= <probe> N) fail))` boundary sweeps: `num-consts` EXCLUDES
// Boolean-sorted constants, and `size`/`num-exprs` are computed over the goal's
// formulas AFTER Z3 splits every top-level conjunction into separate formulas.
// ---------------------------------------------------------------------------

#[test]
fn num_consts_excludes_boolean_constants_like_z3() {
    let mut terms = TermStore::new();
    // (or a b) with a, b : Bool  ->  z3 num-consts = 0 (Bool excluded).
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let ab = terms.mk_or(vec![a, b]);
    assert_eq!(
        count_consts(&terms, &[ab]),
        0,
        "num-consts must exclude Boolean constants (z3: (or a b) -> 0)"
    );

    // Two Int constants  ->  z3 num-consts = 2.
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let eq = terms.mk_eq(x, y);
    assert_eq!(
        count_consts(&terms, &[eq]),
        2,
        "num-consts must count non-Bool (Int) constants (z3: (= x y) -> 2)"
    );

    // Mixed Int + Bool  ->  z3 counts only the two Ints (the Bool p is excluded).
    let p = terms.mk_var("p", Sort::Bool);
    assert_eq!(
        count_consts(&terms, &[eq, p]),
        2,
        "num-consts on a mixed Int+Bool goal must exclude the Bool (z3: -> 2)"
    );
}

#[test]
fn size_and_num_exprs_split_top_level_conjunctions_like_z3() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    // Distinct Int comparisons so the conjunction is a genuine 2-clause `and`.
    let e1 = terms.mk_eq(x, y);
    let z = terms.mk_var("z", Sort::Int);
    let e2 = terms.mk_eq(y, z);
    let conj = terms.mk_and(vec![e1, e2]);

    // z3: `(and A B)` splits into two formulas -> size = 2. (depth is irrelevant
    // to structural probes; pass 0, the depth of a root goal.)
    let size = Probe::Size;
    assert_eq!(
        eval_probe_num(&size, &terms, &[conj], 0),
        2.0,
        "size must count post-split top-level conjuncts (z3: (and A B) -> 2)"
    );

    // num-exprs is computed over the SPLIT formulas, so the top `and` node is
    // NOT counted. Its value equals the count over the two conjuncts directly.
    let num_exprs = Probe::NumExprs;
    let split_count = count_exprs(&terms, &[e1, e2]) as f64;
    assert_eq!(
        eval_probe_num(&num_exprs, &terms, &[conj], 0),
        split_count,
        "num-exprs must exclude the split-away top-level `and` node (z3 goal model)"
    );
    // And it is strictly less than the unsplit count (which would include `and`).
    assert!(
        (eval_probe_num(&num_exprs, &terms, &[conj], 0) as usize) < count_exprs(&terms, &[conj]),
        "splitting the conjunction must drop the `and` node from num-exprs"
    );
}

#[test]
fn flatten_top_conjunctions_is_recursive_but_top_level_only() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let c = terms.mk_var("c", Sort::Bool);
    // Nested top-level and: (and (and a b) c) -> [a, b, c].
    let ab = terms.mk_and(vec![a, b]);
    let nested = terms.mk_and(vec![ab, c]);
    assert_eq!(
        flatten_top_conjunctions(&terms, &[nested]),
        vec![a, b, c],
        "nested top-level conjunctions flatten fully, in order"
    );

    // An `and` UNDER an `or` is NOT top-level: (or (and a b) c) stays one formula
    // (matching z3, which only splits top-level conjunctions).
    let and_ab = terms.mk_and(vec![a, b]);
    let or_top = terms.mk_or(vec![and_ab, c]);
    assert_eq!(
        flatten_top_conjunctions(&terms, &[or_top]),
        vec![or_top],
        "a conjunction nested under an `or` is not split (z3 splits top-level only)"
    );
}

/// Build a battery of ~30 goals, each with a top-level disjunction (clause), so
/// `split-clause` has real work. The disjuncts are drawn from mutually
/// independent, non-complementary atoms so the clause survives normalization as
/// a genuine `or` (never collapsing to a constant or a single literal).
fn build_split_goal(s: &mut Solver, seed: usize) {
    let a = s.declare_const("a", Sort::Bool);
    let b = s.declare_const("b", Sort::Bool);
    let c = s.declare_const("c", Sort::Bool);
    let x = s.declare_const("x", Sort::Int);
    let zero = s.int_const(0);
    let xgt0 = s.gt(x, zero);
    let na = s.not(a);
    let xlt0 = s.lt(x, zero);

    // Independent atoms: no pair is complementary and none is a tautology, so an
    // `or` of DISTINCT picks keeps exactly that many disjuncts.
    let pool = [a, b, c, xgt0];
    // 2..=4 DISTINCT disjuncts (consecutive indices mod 4 are distinct).
    let n_disj = 2 + (seed % 3);
    let mut disjuncts = Vec::new();
    for k in 0..n_disj {
        disjuncts.push(pool[(seed + k) % pool.len()]);
    }
    let clause = s.or_many(&disjuncts);

    // A side constraint (asserted first for some seeds, so the clause is not
    // always assertion #0); some choices force UNSAT to exercise both verdicts.
    let one = s.int_const(1);
    let side = match seed % 5 {
        0 => a,                 // forces a
        1 => na,                // forces ¬a
        2 => s.and(xgt0, xlt0), // x>0 ∧ x<0 : UNSAT side
        3 => c,
        _ => s.eq(x, one),
    };
    if seed.is_multiple_of(2) {
        s.assert_term(side);
        s.assert_term(clause);
    } else {
        s.assert_term(clause);
        s.assert_term(side);
    }
}

#[test]
fn split_clause_disjunction_is_equisatisfiable_over_thirty_goals() {
    // SOUNDNESS (goal preservation as a disjunction): for every goal,
    //   check-sat(original)  ==  (some subgoal is SAT)
    // and the number of subgoals equals the number of disjuncts in the clause.
    let mut mismatches = 0usize;
    for seed in 0..30usize {
        let mut s = Solver::new(Logic::QfLia);
        build_split_goal(&mut s, seed);

        // Original verdict.
        let base = s.check_sat();
        assert!(!base.is_unknown(), "seed {seed}: baseline unknown");
        let base_sat = base.is_sat();

        // The actual number of disjuncts in the (first) surviving clause.
        let ids: Vec<ay_core::TermId> = s.assertions().iter().map(|t| t.0).collect();
        let clause_len = ids
            .iter()
            .find_map(|&id| as_clause(s.terms_mut(), id).map(|d| d.len()))
            .expect("seed goal must contain a surviving clause");

        // Split the clause.
        let subgoals = Tactic::SplitClause
            .apply_goals(s.terms_mut(), root(ids))
            .expect("goal has a clause");
        assert_eq!(
            subgoals.len(),
            clause_len,
            "seed {seed}: subgoal count must equal the disjunct count"
        );

        // Solve each subgoal in the same store (reset + re-assert its formulas).
        let mut any_sub_sat = false;
        for sub in &subgoals {
            s.try_reset_assertions().expect("reset");
            for &id in &sub.formulas {
                s.try_assert_term(Term(id)).expect("assert subgoal formula");
            }
            let r = s.check_sat();
            assert!(!r.is_unknown(), "seed {seed}: subgoal unknown");
            any_sub_sat |= r.is_sat();
        }

        if base_sat != any_sub_sat {
            mismatches += 1;
        }
    }
    assert_eq!(
        mismatches, 0,
        "split-clause must preserve satisfiability as a disjunction on every goal"
    );
}

#[test]
fn from_apply_maps_the_full_combinator_grammar() {
    // The shared registry maps every combinator to an executable tactic (parse →
    // engine), so the SMT-LIB and C-API surfaces cannot drift.
    assert_eq!(Tactic::from_apply(&ApplyTactic::Fail).name(), "fail");
    assert_eq!(
        Tactic::from_apply(&ApplyTactic::SplitClause).name(),
        "split-clause"
    );
    // solve-eqs is ONE primitive (depth 1), not a flatten-and-prefixed sequence.
    assert_eq!(
        Tactic::from_apply(&ApplyTactic::SolveEqs).name(),
        "solve-eqs"
    );
    assert_eq!(
        Tactic::from_apply(&ApplyTactic::OrElse(vec![
            ApplyTactic::Fail,
            ApplyTactic::Simplify
        ]))
        .name(),
        "(or-else fail flatten-and)"
    );
    assert_eq!(
        Tactic::from_apply(&ApplyTactic::Repeat(
            Box::new(ApplyTactic::ElimAnd),
            Some(4)
        ))
        .name(),
        "(repeat flatten-and 4)"
    );
    // try-for / using-params reduce to the wrapped tactic (params/timeout do not
    // change the equivalence-preserving transform).
    assert_eq!(
        Tactic::from_apply(&ApplyTactic::TryFor(Box::new(ApplyTactic::Simplify), 1000)).name(),
        "flatten-and"
    );
    assert_eq!(
        Tactic::from_apply(&ApplyTactic::UsingParams(
            Box::new(ApplyTactic::Simplify),
            vec![]
        ))
        .name(),
        "flatten-and"
    );
}

#[test]
fn from_apply_maps_qe_to_the_cooper_qe_light_engine() {
    // `qe` shares `qe-light`'s Cooper engine arm — the same alias pattern as
    // `simplify`/`elim-and` → `flatten-and`. `name()` therefore reports the
    // engine name (`qe-light`) for a parsed `qe`; this is diagnostics-only, the
    // transform (and its equivalence self-check) is identical.
    assert_eq!(Tactic::from_apply(&ApplyTactic::Qe).name(), "qe-light");
    assert_eq!(Tactic::from_apply(&ApplyTactic::QeLight).name(), "qe-light");
}

#[test]
fn from_apply_maps_propagate_ineqs_to_its_own_tactic_not_skip() {
    // LOCK against silent regression: `ApplyTactic` is #[non_exhaustive] and
    // `from_apply` ends in `_ => Tactic::Skip`, so a forgotten mapping arm
    // would silently turn `propagate-ineqs` into the identity with no compile
    // error. Pin the mapping AND that the tactic actually transforms a
    // subsumable goal (which `skip` never would).
    let t = Tactic::from_apply(&ApplyTactic::PropagateIneqs);
    assert!(
        matches!(t, Tactic::PropagateIneqs),
        "propagate-ineqs must map to its own tactic, got {}",
        t.name()
    );
    assert_eq!(t.name(), "propagate-ineqs");

    let mut terms = TermStore::new();
    let x = terms.mk_var("x", ay_core::Sort::Int);
    let five = terms.mk_int(num_bigint::BigInt::from(5));
    let ten = terms.mk_int(num_bigint::BigInt::from(10));
    let le5 = terms.mk_le(x, five);
    let le10 = terms.mk_le(x, ten);

    let mut goal = vec![le5, le10];
    let progressed = t.apply(&mut terms, &mut goal);
    assert!(
        progressed,
        "the weaker bound must be dropped (not a skip no-op)"
    );
    assert_eq!(goal, vec![le5], "only the stronger bound survives");
}

// ---------------------------------------------------------------------------
// DIFFERENTIAL / EQUIVALENCE: same verdict with vs. without the tactic.
// ---------------------------------------------------------------------------

/// Build a goal containing nested ANDs into the given solver and return the
/// verdict. `which` selects one of several sat/unsat shapes.
///
/// Each shape asserts a top-level `(and (and ...) ...)` so flatten-and has real
/// work to do. The shapes are constructed identically regardless of solver, so
/// the only difference between the baseline and tactic runs is whether the
/// tactic transformation is applied first.
fn build_goal(s: &mut Solver, which: usize) {
    let a = s.declare_const(&format!("a{which}"), Sort::Bool);
    let b = s.declare_const(&format!("b{which}"), Sort::Bool);
    let c = s.declare_const(&format!("c{which}"), Sort::Bool);
    let x = s.declare_const(&format!("x{which}"), Sort::Int);
    let zero = s.int_const(0);
    let one = s.int_const(1);
    let two = s.int_const(2);

    match which {
        // --- SAT shapes ---
        0 => {
            // (and (and a b) c) — plainly SAT (all true).
            let inner = s.and(a, b);
            let g = s.and(inner, c);
            s.assert_term(g);
        }
        1 => {
            // (and (and (x>0) (x<2)) (a or b)) — SAT (x=1).
            let xgt = s.gt(x, zero);
            let xlt = s.lt(x, two);
            let inner = s.and(xgt, xlt);
            let ab = s.or(a, b);
            let g = s.and(inner, ab);
            s.assert_term(g);
        }
        2 => {
            // (and (and (x>=0) (x<=1)) (and (a) (not b))) — SAT.
            let xge = s.ge(x, zero);
            let xle = s.le(x, one);
            let i1 = s.and(xge, xle);
            let nb = s.not(b);
            let i2 = s.and(a, nb);
            let g = s.and(i1, i2);
            s.assert_term(g);
        }
        3 => {
            // Deeply nested all-true conjunction — SAT.
            let i1 = s.and(a, b);
            let i2 = s.and(i1, c);
            let xge = s.ge(x, zero);
            let i3 = s.and(i2, xge);
            s.assert_term(i3);
        }
        4 => {
            // (and (and (x=1) (a)) (or b c)) — SAT.
            let xeq = s.eq(x, one);
            let i1 = s.and(xeq, a);
            let bc = s.or(b, c);
            let g = s.and(i1, bc);
            s.assert_term(g);
        }
        // --- UNSAT shapes ---
        5 => {
            // (and (and a (not a)) b) — UNSAT (a ∧ ¬a).
            let na = s.not(a);
            let inner = s.and(a, na);
            let g = s.and(inner, b);
            s.assert_term(g);
        }
        6 => {
            // (and (and (x>1) (x<1)) c) — UNSAT (empty int interval).
            let xgt = s.gt(x, one);
            let xlt = s.lt(x, one);
            let inner = s.and(xgt, xlt);
            let g = s.and(inner, c);
            s.assert_term(g);
        }
        7 => {
            // (and (and (x=0) (x=1)) a) — UNSAT (x can't be both).
            let e0 = s.eq(x, zero);
            let e1 = s.eq(x, one);
            let inner = s.and(e0, e1);
            let g = s.and(inner, a);
            s.assert_term(g);
        }
        8 => {
            // (and (and (and a b) (not b)) c) — UNSAT (b ∧ ¬b).
            let i1 = s.and(a, b);
            let nb = s.not(b);
            let i2 = s.and(i1, nb);
            let g = s.and(i2, c);
            s.assert_term(g);
        }
        _ => {
            // (and (and (x>=2) (a)) (and (x<=0) (b))) — UNSAT.
            let xge = s.ge(x, two);
            let i1 = s.and(xge, a);
            let xle = s.le(x, zero);
            let i2 = s.and(xle, b);
            let g = s.and(i1, i2);
            s.assert_term(g);
        }
    }
}

#[test]
fn tactic_solver_verdict_matches_baseline_on_nested_ands() {
    // Shapes 0..=4 are SAT, 5..=9 are UNSAT.
    let expected_sat = [
        true, true, true, true, true, false, false, false, false, false,
    ];

    for (which, should_be_sat) in expected_sat.iter().copied().enumerate() {
        // Baseline: solve the untransformed goal.
        let mut baseline = Solver::new(Logic::QfLia);
        build_goal(&mut baseline, which);
        let base_result = baseline.check_sat();

        // Tactic path: apply flatten-and (then flatten-and, exercising `then`)
        // before solving.
        let tactic = Tactic::flatten_and().then(Tactic::flatten_and());
        let mut tsolver = tactic.solver(Logic::QfLia).expect("tactic solver");
        build_goal(tsolver.solver_mut(), which);
        let tactic_result = tsolver.check_sat();

        assert!(
            !base_result.is_unknown(),
            "baseline returned Unknown for shape {which}"
        );
        assert!(
            !tactic_result.is_unknown(),
            "tactic returned Unknown for shape {which}"
        );

        // Identical verdicts between baseline and tactic path. SolveResult is
        // not Copy (Unsat carries a proof certificate), so compare by reference.
        assert_eq!(
            base_result.result(),
            tactic_result.result(),
            "verdict mismatch for shape {which}: baseline={:?} tactic={:?}",
            base_result.result(),
            tactic_result.result(),
        );

        // And both match the independently-known expected verdict. (SolveResult
        // cannot be constructed for comparison — Unsat carries a proof
        // certificate — so check via is_sat/is_unsat.)
        if should_be_sat {
            assert!(
                tactic_result.is_sat(),
                "shape {which} expected SAT, got {:?}",
                tactic_result.result()
            );
        } else {
            assert!(
                tactic_result.is_unsat(),
                "shape {which} expected UNSAT, got {:?}",
                tactic_result.result()
            );
        }
    }
}

#[test]
fn tactic_solver_actually_flattens_the_goal_before_solving() {
    // A single top-level (and (and a b) c) should become 3 separate assertions
    // after the tactic runs (observable via the solver's assertion list).
    let tactic = Tactic::flatten_and();
    let mut tsolver = tactic.solver(Logic::QfLia).expect("tactic solver");
    {
        let s = tsolver.solver_mut();
        let a = s.declare_const("a", Sort::Bool);
        let b = s.declare_const("b", Sort::Bool);
        let c = s.declare_const("c", Sort::Bool);
        let inner = s.and(a, b);
        let g = s.and(inner, c);
        s.assert_term(g);
    }
    assert_eq!(
        tsolver.assertions().len(),
        1,
        "before solving: one AND goal"
    );

    let result = tsolver.check_sat();
    assert!(result.is_sat());
    // After check_sat ran the tactic, the goal was rewritten to 3 conjuncts.
    assert_eq!(
        tsolver.assertions().len(),
        3,
        "after tactic: AND flattened into 3 assertions"
    );
}

// ---------------------------------------------------------------------------
// qe-light: the standalone Cooper LIA QE reached through the tactic surface.
// ---------------------------------------------------------------------------

#[test]
fn tactic_qe_light_name_is_stable() {
    assert_eq!(Tactic::qe_light().name(), "qe-light");
    assert_eq!(
        Tactic::flatten_and().then(Tactic::qe_light()).name(),
        "(then flatten-and qe-light)"
    );
}

/// Whether a top-level assertion is still a quantifier node.
fn is_quantifier(s: &Solver, t: crate::api::Term) -> bool {
    use crate::api::TermKind;
    matches!(s.term_kind(t), TermKind::Forall | TermKind::Exists)
}

/// Build `(exists ((x Int)) (and (x > y) (x < y + 10)))` — always SAT (e.g.
/// x = y+1), an in-fragment eliminable existential.
fn assert_eliminable_sat_exists(s: &mut Solver) {
    let x = s.declare_const("x", Sort::Int);
    let y = s.declare_const("y", Sort::Int);
    let ten = s.int_const(10);
    let yp10 = s.add(y, ten);
    let l1 = s.gt(x, y);
    let l2 = s.lt(x, yp10);
    let body = s.and(l1, l2);
    let ex = s.try_exists(&[x], body).expect("build exists");
    s.assert_term(ex);
}

/// Build `(exists ((x Int)) (and (x > y) (x < y)))` — UNSAT (no integer strictly
/// between y and y), also in-fragment.
fn assert_eliminable_unsat_exists(s: &mut Solver) {
    let x = s.declare_const("x", Sort::Int);
    let y = s.declare_const("y", Sort::Int);
    let l1 = s.gt(x, y);
    let l2 = s.lt(x, y);
    let body = s.and(l1, l2);
    let ex = s.try_exists(&[x], body).expect("build exists");
    s.assert_term(ex);
}

#[test]
fn tactic_qe_light_eliminates_quantifier_and_matches_baseline_sat() {
    // Baseline: solve the quantified goal directly (quantified LIA decides it).
    let mut baseline = Solver::new(Logic::Lia);
    assert_eliminable_sat_exists(&mut baseline);
    let base = baseline.check_sat();
    assert!(base.is_sat(), "baseline exists should be SAT");

    // Tactic path: qe-light rewrites the goal first.
    let mut t = Tactic::qe_light()
        .solver(Logic::Lia)
        .expect("qe-light solver");
    assert_eliminable_sat_exists(t.solver_mut());

    // Before solving: the single assertion is a quantifier.
    let before = t.assertions();
    assert_eq!(before.len(), 1);
    assert!(
        is_quantifier(t.solver(), before[0]),
        "before qe-light the assertion is an existential"
    );

    let res = t.check_sat();

    // DIFFERENTIAL: same verdict as the untransformed baseline.
    assert!(!res.is_unknown(), "qe-light path returned Unknown");
    assert_eq!(
        base.result(),
        res.result(),
        "qe-light verdict must match baseline: base={:?} qe={:?}",
        base.result(),
        res.result()
    );
    assert!(res.is_sat());

    // The quantifier is GONE: no remaining assertion is a quantifier node.
    for a in t.assertions() {
        assert!(
            !is_quantifier(t.solver(), a),
            "qe-light must remove the eliminable existential"
        );
    }
}

#[test]
fn tactic_qe_light_eliminates_quantifier_and_matches_baseline_unsat() {
    let mut baseline = Solver::new(Logic::Lia);
    assert_eliminable_unsat_exists(&mut baseline);
    let base = baseline.check_sat();
    assert!(
        base.is_unsat(),
        "baseline empty-interval exists should be UNSAT"
    );

    let mut t = Tactic::qe_light()
        .solver(Logic::Lia)
        .expect("qe-light solver");
    assert_eliminable_unsat_exists(t.solver_mut());
    let res = t.check_sat();

    assert!(!res.is_unknown());
    assert_eq!(
        base.result(),
        res.result(),
        "qe-light UNSAT verdict must match baseline"
    );
    assert!(res.is_unsat());

    for a in t.assertions() {
        assert!(
            !is_quantifier(t.solver(), a),
            "qe-light must remove the eliminable existential"
        );
    }
}

#[test]
fn tactic_qe_light_leaves_out_of_fragment_quantifier_intact() {
    // ∃x,y. x < y — two bound variables is out of Cooper's single-var fragment.
    // qe-light makes NO progress and leaves the quantifier intact; the verdict
    // is still correct (decided by the quantified-LIA solver), matching baseline.
    let mut baseline = Solver::new(Logic::Lia);
    let xb = baseline.declare_const("x", Sort::Int);
    let yb = baseline.declare_const("y", Sort::Int);
    let bodyb = baseline.lt(xb, yb);
    let exb = baseline.try_exists(&[xb, yb], bodyb).expect("build exists");
    baseline.assert_term(exb);
    let base = baseline.check_sat();

    let mut t = Tactic::qe_light()
        .solver(Logic::Lia)
        .expect("qe-light solver");
    {
        let s = t.solver_mut();
        let x = s.declare_const("x", Sort::Int);
        let y = s.declare_const("y", Sort::Int);
        let body = s.lt(x, y);
        let ex = s.try_exists(&[x, y], body).expect("build exists");
        s.assert_term(ex);
    }

    let res = t.check_sat();
    assert_eq!(
        base.result(),
        res.result(),
        "out-of-fragment verdict must match baseline"
    );
    // The (uneliminated) existential is still present: identity on out-of-fragment.
    assert_eq!(t.assertions().len(), 1);
    assert!(
        is_quantifier(t.solver(), t.assertions()[0]),
        "out-of-fragment existential must be left intact"
    );
}

// ---------------------------------------------------------------------------
// nnf EQUIVALENCE differential: over ~30 random Boolean formulas, the input and
// its NNF agree on every model (`input XOR nnf(input)` is UNSAT). NNF is
// equivalence-preserving — strictly stronger than the equisatisfiability the
// tactic surface requires — so this is the soundness property for `nnf`. The
// printed shapes were additionally cross-checked against z3 4.15.4's
// `(apply nnf)` during review (0 disagreement).
// ---------------------------------------------------------------------------

/// A tiny deterministic xorshift PRNG (reproducible, no external deps).
struct NnfRng(u64);

impl NnfRng {
    fn new(seed: u64) -> Self {
        NnfRng(seed | 1)
    }
    fn next_u64(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }
    fn below(&mut self, n: usize) -> usize {
        (self.next_u64() % n as u64) as usize
    }
}

/// Is `id` an atom (not a Boolean connective the NNF pass must eliminate / a
/// node under which a negation may not sit)?
fn nnf_is_atom(terms: &TermStore, id: ay_core::TermId) -> bool {
    use ay_core::term::TermData;
    match terms.get(id) {
        TermData::App(sym, args) => match sym.name() {
            "and" | "or" | "=>" | "xor" => false,
            "=" => args.first().is_none_or(|&a| terms.sort(a) != &Sort::Bool),
            _ => true,
        },
        TermData::Not(_) => false,
        TermData::Ite(..) => terms.sort(id) != &Sort::Bool,
        TermData::Forall(..) | TermData::Exists(..) => false,
        _ => true,
    }
}

/// Is `id` in negation normal form?
fn nnf_is_nnf(terms: &TermStore, id: ay_core::TermId) -> bool {
    use ay_core::term::TermData;
    match terms.get(id).clone() {
        TermData::Const(_) | TermData::Var(_, _) => true,
        TermData::Not(inner) => nnf_is_atom(terms, inner),
        TermData::Ite(..) if terms.sort(id) == &Sort::Bool => false,
        TermData::Ite(..) => true,
        TermData::App(sym, args) => match sym.name() {
            "and" | "or" => args.iter().all(|&a| nnf_is_nnf(terms, a)),
            "=>" | "xor" => false,
            "=" if args.first().is_some_and(|&a| terms.sort(a) == &Sort::Bool) => false,
            _ => true,
        },
        TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => nnf_is_nnf(terms, body),
        _ => true,
    }
}

/// Declare the shared atom pool: four Bool constants plus two non-Bool atoms
/// (`x > 0`, `x = 3`) so the pass must both keep and negate genuine atoms.
fn nnf_atoms(s: &mut Solver) -> Vec<ay_core::TermId> {
    let a = s.declare_const("a", Sort::Bool).0;
    let b = s.declare_const("b", Sort::Bool).0;
    let c = s.declare_const("c", Sort::Bool).0;
    let d = s.declare_const("d", Sort::Bool).0;
    let x = s.declare_const("x", Sort::Int);
    let zero = s.int_const(0);
    let three = s.int_const(3);
    let gt = s.gt(x, zero).0;
    let eqx = s.eq(x, three).0;
    vec![a, b, c, d, gt, eqx]
}

/// Build a random Boolean formula, exercising every connective the NNF pass
/// eliminates (`=>` via its or-form, `xor`, bool `=`, bool `ite`) plus
/// `and`/`or` and *raw* negations (`mk_not_raw`, so the pass — not the builder —
/// performs the De Morgan pushdown).
fn nnf_gen(
    terms: &mut TermStore,
    atoms: &[ay_core::TermId],
    rng: &mut NnfRng,
    depth: usize,
) -> ay_core::TermId {
    use ay_core::term::Symbol;
    if depth == 0 || rng.below(3) == 0 {
        return atoms[rng.below(atoms.len())];
    }
    match rng.below(7) {
        0 => {
            let x = nnf_gen(terms, atoms, rng, depth - 1);
            terms.mk_not_raw(x)
        }
        1 => {
            let l = nnf_gen(terms, atoms, rng, depth - 1);
            let r = nnf_gen(terms, atoms, rng, depth - 1);
            terms.mk_and(vec![l, r])
        }
        2 => {
            let l = nnf_gen(terms, atoms, rng, depth - 1);
            let r = nnf_gen(terms, atoms, rng, depth - 1);
            terms.mk_or(vec![l, r])
        }
        3 => {
            let l = nnf_gen(terms, atoms, rng, depth - 1);
            let r = nnf_gen(terms, atoms, rng, depth - 1);
            terms.mk_implies(l, r)
        }
        4 => {
            let l = nnf_gen(terms, atoms, rng, depth - 1);
            let r = nnf_gen(terms, atoms, rng, depth - 1);
            terms.mk_xor(l, r)
        }
        5 => {
            let l = nnf_gen(terms, atoms, rng, depth - 1);
            let r = nnf_gen(terms, atoms, rng, depth - 1);
            terms.mk_app(Symbol::named("="), vec![l, r], Sort::Bool)
        }
        _ => {
            let cnd = nnf_gen(terms, atoms, rng, depth - 1);
            let l = nnf_gen(terms, atoms, rng, depth - 1);
            let r = nnf_gen(terms, atoms, rng, depth - 1);
            terms.mk_ite_raw(cnd, l, r)
        }
    }
}

#[test]
fn nnf_is_equivalence_preserving_over_thirty_random_bool_formulas() {
    let mut non_nnf = 0usize;
    let mut disagreements = 0usize;
    let mut unknowns = 0usize;

    for seed in 0..30u64 {
        let mut s = Solver::new(Logic::QfLia);
        let atoms = nnf_atoms(&mut s);
        let mut rng = NnfRng::new(
            seed.wrapping_mul(0x9E37_79B9_7F4A_7C15)
                .wrapping_add(0xABCD),
        );
        let f = nnf_gen(s.terms_mut(), &atoms, &mut rng, 3);

        // The tactic result goal (NNF rewrite + top-level `and` split).
        let goals = Tactic::Nnf
            .apply_goals(s.terms_mut(), root(vec![f]))
            .expect("nnf never fails");
        assert_eq!(goals.len(), 1, "seed {seed}: nnf yields a single goal");

        // Every produced formula must genuinely be in NNF.
        for &g in &goals[0].formulas {
            if !nnf_is_nnf(s.terms_mut(), g) {
                non_nnf += 1;
            }
        }

        // Reconstruct the goal as one conjunction and test that F ⊕ R is UNSAT.
        let result = s.terms_mut().mk_and(goals[0].formulas.clone());
        let diff = {
            let t = s.terms_mut();
            let nf = t.mk_not(f);
            let nr = t.mk_not(result);
            let left = t.mk_and(vec![f, nr]);
            let right = t.mk_and(vec![nf, result]);
            t.mk_or(vec![left, right])
        };
        s.try_reset_assertions().expect("reset");
        s.try_assert_term(Term(diff)).expect("assert diff");
        let res = s.check_sat();
        if res.is_unknown() {
            unknowns += 1;
        } else if !res.is_unsat() {
            disagreements += 1;
        }
    }

    assert_eq!(
        non_nnf, 0,
        "every nnf output formula must be in negation normal form"
    );
    assert_eq!(
        unknowns, 0,
        "the equivalence check must be decided on every formula"
    );
    assert_eq!(
        disagreements, 0,
        "nnf must be equivalence-preserving: input XOR nnf(input) must be UNSAT on all formulas"
    );
}
// ---------------------------------------------------------------------------
// tseitin-cnf SOUNDNESS: equisatisfiability over a battery of random formulas.
//
// The pass introduces fresh aux vars, so the CNF is EQUISATISFIABLE (not
// equivalent) to the input. We verify the property the solver relies on:
//   check-sat(F)  ==  check-sat(CNF(F))   [aux vars free]
// by producing the CNF with the pass and solving the ACTUAL clauses directly.
// ---------------------------------------------------------------------------

/// A Boolean *connective* Tseitin must decompose (anything else is an atom).
fn tseitin_is_connective(terms: &TermStore, id: TermId) -> bool {
    match terms.get(id) {
        TermData::Not(_) => true,
        TermData::Ite(..) => terms.sort(id) == &Sort::Bool,
        TermData::App(sym, args) => match sym.name() {
            "and" | "or" | "xor" | "=>" | "implies" => true,
            "=" => args.len() == 2 && terms.sort(args[0]) == &Sort::Bool,
            "distinct" => args.len() >= 2 && terms.sort(args[0]) == &Sort::Bool,
            _ => false,
        },
        _ => false,
    }
}

/// A literal: an atom or a single negation of an atom.
fn tseitin_is_literal(terms: &TermStore, id: TermId) -> bool {
    let inner = match terms.get(id) {
        TermData::Not(x) => *x,
        _ => id,
    };
    !tseitin_is_connective(terms, inner)
}

/// A clause: a literal, a flat `or` of literals, or a Boolean constant.
fn tseitin_is_clause(terms: &TermStore, id: TermId) -> bool {
    match terms.get(id) {
        TermData::App(sym, args) if sym.name() == "or" => {
            args.iter().all(|&a| tseitin_is_literal(terms, a))
        }
        _ => tseitin_is_literal(terms, id),
    }
}

/// Deterministic SplitMix-style PRNG so the battery is reproducible.
fn tseitin_next(state: &mut u64) -> u64 {
    *state = state.wrapping_add(0x9E37_79B9_7F4A_7C15);
    let mut z = *state;
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

/// Build a random Boolean formula of bounded depth over `vars`.
fn tseitin_build_formula(s: &mut Solver, vars: &[Term], state: &mut u64, depth: u32) -> Term {
    let r = tseitin_next(state);
    if depth == 0 || r.is_multiple_of(5) {
        match r % 8 {
            0 => s.bool_const(true),
            1 => s.bool_const(false),
            n => {
                let v = vars[(n as usize) % vars.len()];
                if r & 0x100 != 0 {
                    s.not(v)
                } else {
                    v
                }
            }
        }
    } else {
        let a = tseitin_build_formula(s, vars, state, depth - 1);
        let b = tseitin_build_formula(s, vars, state, depth - 1);
        match r % 6 {
            0 => s.and(a, b),
            1 => s.or(a, b),
            2 => s.not(a),
            3 => s.xor(a, b),
            4 => s.iff(a, b),
            _ => {
                let c = tseitin_build_formula(s, vars, state, depth - 1);
                s.ite(a, b, c)
            }
        }
    }
}

#[test]
fn tseitin_cnf_is_equisatisfiable_over_random_formulas() {
    // GOAL PRESERVATION as a SOUNDNESS property: for every random formula F,
    //   check-sat(F)  ==  check-sat(CNF(F))     [aux vars free]
    // The CNF is produced by the pass and solved directly (reset + re-assert its
    // clauses), so this exercises the ACTUAL clausal output — and the output is
    // asserted to be genuinely clausal. The battery must hit BOTH verdicts.
    let mut mismatches = 0usize;
    let mut saw_sat = false;
    let mut saw_unsat = false;

    for seed in 0..40u64 {
        let mut s = Solver::new(Logic::QfUf);
        let a = s.declare_const("a", Sort::Bool);
        let b = s.declare_const("b", Sort::Bool);
        let c = s.declare_const("c", Sort::Bool);
        let d = s.declare_const("d", Sort::Bool);
        let vars = [a, b, c, d];

        let mut state = seed.wrapping_mul(0xD1B5_4A32_D192_ED03).wrapping_add(1);
        let f = tseitin_build_formula(&mut s, &vars, &mut state, 4);

        // Verdict of the ORIGINAL goal.
        s.assert_term(f);
        let base = s.check_sat();
        assert!(!base.is_unknown(), "seed {seed}: baseline unknown");
        let base_sat = base.is_sat();

        // Produce the CNF of {F} with the pass, in the SAME term store.
        let mut cnf = vec![f.0];
        let _changed = Tactic::TseitinCnf.apply(s.terms_mut(), &mut cnf);
        for &clause in &cnf {
            assert!(
                tseitin_is_clause(s.terms_mut(), clause),
                "seed {seed}: CNF formula is not a clause: {:?}",
                s.terms_mut().get(clause)
            );
        }

        // Solve the CNF directly (aux vars are free Boolean constants).
        s.try_reset_assertions().expect("reset");
        for &id in &cnf {
            s.try_assert_term(Term(id)).expect("assert cnf clause");
        }
        let cnf_res = s.check_sat();
        assert!(!cnf_res.is_unknown(), "seed {seed}: cnf unknown");
        let cnf_sat = cnf_res.is_sat();

        if base_sat != cnf_sat {
            mismatches += 1;
        }
        if base_sat {
            saw_sat = true;
        } else {
            saw_unsat = true;
        }
    }

    assert_eq!(
        mismatches, 0,
        "tseitin-cnf must preserve satisfiability on every random formula"
    );
    assert!(
        saw_sat && saw_unsat,
        "battery must exercise BOTH verdicts (sat AND unsat preserved): \
         saw_sat={saw_sat} saw_unsat={saw_unsat}"
    );
}

// ---------------------------------------------------------------------------
// bit-blast EQUISATISFIABILITY differential: solve QF_BV goals WITH the
// bit-blast tactic (which actually rewrites the assertions to a pure-Boolean
// goal and solves that) and WITHOUT it, and require identical SAT/UNSAT
// verdicts. Because the tactic-solver replaces the goal with its blasted form
// before check_sat, this is a genuine end-to-end equisatisfiability test of the
// blasted Boolean goal against the original bit-vector goal.
// ---------------------------------------------------------------------------

/// Build QF_BV goal `which` (0..=7). Shapes 0..=3 are SAT, 4..=7 are UNSAT.
fn build_bv_goal(s: &mut Solver, which: usize) {
    let x = s.bv_var("x", 4);
    let y = s.bv_var("y", 4);
    match which {
        0 => {
            // x < y  ∧  y < x+x   (satisfiable, e.g. x=1,y=2 with 1<2<... )
            let lt1 = s.bvult(x, y);
            let xx = s.bvadd(x, x);
            let lt2 = s.bvult(y, xx);
            let g = s.and(lt1, lt2);
            s.assert_term(g);
        }
        1 => {
            // (x & y) = (y & x)   — always true, SAT.
            let axy = s.bvand(x, y);
            let ayx = s.bvand(y, x);
            let eq = s.eq(axy, ayx);
            s.assert_term(eq);
        }
        2 => {
            // x + y = 5   — SAT.
            let sum = s.bvadd(x, y);
            let five = s.bv_const(5, 4);
            let eq = s.eq(sum, five);
            s.assert_term(eq);
        }
        3 => {
            // (x ^ y) != 0 for some x,y — SAT.
            let xor = s.bvxor(x, y);
            let zero = s.bv_const(0, 4);
            let eq = s.eq(xor, zero);
            let ne = s.not(eq);
            s.assert_term(ne);
        }
        4 => {
            // x = x + 1   — UNSAT (no fixpoint of increment).
            let one = s.bv_const(1, 4);
            let inc = s.bvadd(x, one);
            let eq = s.eq(x, inc);
            s.assert_term(eq);
        }
        5 => {
            // x < y  ∧  y < x   — UNSAT.
            let lt1 = s.bvult(x, y);
            let lt2 = s.bvult(y, x);
            let g = s.and(lt1, lt2);
            s.assert_term(g);
        }
        6 => {
            // (x & y) != (y & x)   — UNSAT (bvand is commutative).
            let axy = s.bvand(x, y);
            let ayx = s.bvand(y, x);
            let eq = s.eq(axy, ayx);
            let ne = s.not(eq);
            s.assert_term(ne);
        }
        _ => {
            // x - x != 0   — UNSAT.
            let sub = s.bvsub(x, x);
            let zero = s.bv_const(0, 4);
            let eq = s.eq(sub, zero);
            let ne = s.not(eq);
            s.assert_term(ne);
        }
    }
}

#[test]
fn bit_blast_tactic_solver_verdict_matches_baseline_on_qf_bv() {
    let expected_sat = [true, true, true, true, false, false, false, false];

    for (which, should_be_sat) in expected_sat.iter().copied().enumerate() {
        // Baseline: solve the untransformed QF_BV goal.
        let mut baseline = Solver::new(Logic::QfBv);
        build_bv_goal(&mut baseline, which);
        let base = baseline.check_sat();

        // Tactic path: bit-blast rewrites the goal to a pure-Boolean goal and the
        // solver decides THAT (verified equisatisfiable to the original here).
        let mut tsolver = Tactic::BitBlast.solver(Logic::QfBv).expect("tactic solver");
        build_bv_goal(tsolver.solver_mut(), which);
        let tactic = tsolver.check_sat();

        assert!(!base.is_unknown(), "baseline Unknown for shape {which}");
        assert!(!tactic.is_unknown(), "bit-blast Unknown for shape {which}");
        assert_eq!(
            base.result(),
            tactic.result(),
            "bit-blast verdict mismatch for shape {which}: baseline={:?} tactic={:?}",
            base.result(),
            tactic.result(),
        );
        if should_be_sat {
            assert!(tactic.is_sat(), "shape {which} expected SAT");
        } else {
            assert!(tactic.is_unsat(), "shape {which} expected UNSAT");
        }
    }
}

#[test]
fn bit_blast_tactic_solver_actually_blasts_before_solving() {
    // After the tactic runs, the goal must be pure Boolean (no BV-sorted term in
    // the solver's assertions), demonstrating the blast really happened.
    let mut tsolver = Tactic::BitBlast.solver(Logic::QfBv).expect("tactic solver");
    build_bv_goal(tsolver.solver_mut(), 0);
    let _ = tsolver.check_sat();
    for t in tsolver.assertions() {
        assert!(
            !matches!(tsolver.solver().term_sort(t), Sort::BitVec(_)),
            "after bit-blast the goal must contain no BV-sorted assertion"
        );
    }
}

#[test]
fn bit_blast_tactic_solver_honestly_fails_on_out_of_fragment() {
    // HONESTY: a bit-blast tactic-solver on an OUT-OF-FRAGMENT goal (bvudiv) must
    // NOT fabricate a verdict — the tactic produces no goal, so the solver
    // surfaces Unknown rather than silently solving the untransformed goal. This
    // is the property the FFI/ayz3 Tactic('bit-blast') path relies on to raise.
    let mut tsolver = Tactic::BitBlast.solver(Logic::QfBv).expect("tactic solver");
    {
        let s = tsolver.solver_mut();
        let x = s.bv_var("x", 4);
        let y = s.bv_var("y", 4);
        let div = s.bvudiv(x, y);
        let one = s.bv_const(1, 4);
        let eq = s.eq(div, one);
        s.assert_term(eq);
    }
    let res = tsolver.check_sat();
    assert!(
        res.is_unknown(),
        "bit-blast on an out-of-fragment bvudiv goal must surface Unknown (honest \
         failure), not a fabricated sat/unsat verdict; got {:?}",
        res.result()
    );
}

// ---------------------------------------------------------------------------
// ctx-solver-simplify: contextual simplification USING THE SOLVER.
//
// A top-level assertion the OTHER assertions PROVE redundant is dropped; a
// PROVEN contradiction collapses the goal to `{false}`; an unproven implication
// (SAT or unknown sub-check) never simplifies. The result is EQUIVALENT to the
// input. Shapes were cross-checked against z3 4.15.4 (`(apply
// ctx-solver-simplify)`): AY matches z3 on the contradiction / bool-redundant /
// or-with-eq / dup / valid-only cases, and is order-insensitively MORE
// aggressive than z3 4.15.4 on `{(= x 5),(> x 3)}` (AY drops the redundant
// `(> x 3)`; z3 4.15.4 happens to keep it) — both goals are logically
// equivalent to the input.
// ---------------------------------------------------------------------------

/// Conjoin a goal's formula list into one Bool term (an empty goal is `true`).
fn css_conjoin(terms: &mut TermStore, fs: &[TermId]) -> TermId {
    match fs {
        [] => terms.mk_bool(true),
        [single] => *single,
        many => terms.mk_and(many.to_vec()),
    }
}

/// Assert that `ctx-solver-simplify` applied to `input` yields a goal LOGICALLY
/// EQUIVALENT to it, by checking `input XOR output` is UNSAT in `s`. Returns the
/// produced goal's formula list (so callers can also assert its exact shape).
/// A `true` return of the second tuple field means the pass changed the goal.
fn css_apply_checked(s: &mut Solver, input: Vec<TermId>) -> (Vec<TermId>, bool) {
    let input_conj = css_conjoin(s.terms_mut(), &input);
    let goals = Tactic::CtxSolverSimplify
        .apply_goals(s.terms_mut(), root(input.clone()))
        .expect("ctx-solver-simplify never fails");
    assert_eq!(goals.len(), 1, "ctx-solver-simplify yields a single goal");
    let out = goals[0].formulas.clone();
    let changed = out != input;

    let output_conj = css_conjoin(s.terms_mut(), &out);
    let diff = {
        let t = s.terms_mut();
        let ni = t.mk_not(input_conj);
        let no = t.mk_not(output_conj);
        let left = t.mk_and(vec![input_conj, no]);
        let right = t.mk_and(vec![ni, output_conj]);
        t.mk_or(vec![left, right])
    };
    s.try_reset_assertions().expect("reset");
    s.try_assert_term(Term(diff)).expect("assert diff");
    let res = s.check_sat();
    assert!(
        res.is_unsat(),
        "ctx-solver-simplify must be equivalence-preserving: input XOR output must \
         be UNSAT (got {:?}); input={input:?} output={out:?}",
        res.result()
    );
    (out, changed)
}

#[test]
fn ctx_solver_simplify_name_is_stable() {
    assert_eq!(Tactic::CtxSolverSimplify.name(), "ctx-solver-simplify");
    assert_eq!(
        Tactic::flatten_and().then(Tactic::CtxSolverSimplify).name(),
        "(then flatten-and ctx-solver-simplify)"
    );
    // Resolves through the shared front-end registry (same surface as the C-API).
    assert_eq!(
        Tactic::from_apply(&ApplyTactic::CtxSolverSimplify).name(),
        "ctx-solver-simplify"
    );
}

#[test]
fn ctx_solver_simplify_drops_redundant_literal() {
    // {(> x 3), (= x 5)} : (= x 5) proves (> x 3) redundant -> drop it.
    let mut s = Solver::new(Logic::QfLia);
    let x = s.declare_const("x", Sort::Int).0;
    let three = s.int_const(3).0;
    let five = s.int_const(5).0;
    let gt = s.terms_mut().mk_app(
        ay_core::term::Symbol::named(">"),
        vec![x, three],
        Sort::Bool,
    );
    let eq = s
        .terms_mut()
        .mk_app(ay_core::term::Symbol::named("="), vec![x, five], Sort::Bool);

    let (out, changed) = css_apply_checked(&mut s, vec![gt, eq]);
    assert!(changed, "the redundant (> x 3) must be dropped");
    assert_eq!(out, vec![eq], "only (= x 5) should remain");
}

#[test]
fn ctx_solver_simplify_drops_later_redundant_literal_order_insensitive() {
    // {(= x 5), (> x 3)} : AY is order-insensitive and drops the (later)
    // redundant (> x 3) too (z3 4.15.4 keeps it in this order; both equivalent).
    let mut s = Solver::new(Logic::QfLia);
    let x = s.declare_const("x", Sort::Int).0;
    let three = s.int_const(3).0;
    let five = s.int_const(5).0;
    let eq = s
        .terms_mut()
        .mk_app(ay_core::term::Symbol::named("="), vec![x, five], Sort::Bool);
    let gt = s.terms_mut().mk_app(
        ay_core::term::Symbol::named(">"),
        vec![x, three],
        Sort::Bool,
    );

    let (out, changed) = css_apply_checked(&mut s, vec![eq, gt]);
    assert!(changed);
    assert_eq!(out, vec![eq], "only (= x 5) should remain");
}

#[test]
fn ctx_solver_simplify_collapses_contradiction_to_false() {
    // {(= x 5), (< x 3)} : the context proves the goal UNSAT -> {false}.
    let mut s = Solver::new(Logic::QfLia);
    let x = s.declare_const("x", Sort::Int).0;
    let five = s.int_const(5).0;
    let three = s.int_const(3).0;
    let eq = s
        .terms_mut()
        .mk_app(ay_core::term::Symbol::named("="), vec![x, five], Sort::Bool);
    let lt = s.terms_mut().mk_app(
        ay_core::term::Symbol::named("<"),
        vec![x, three],
        Sort::Bool,
    );

    let (out, changed) = css_apply_checked(&mut s, vec![eq, lt]);
    assert!(changed);
    assert_eq!(out.len(), 1, "an unsat goal collapses to a single formula");
    assert!(
        is_false_literal(s.terms(), out[0]),
        "the collapsed goal must be the literal false"
    );
}

#[test]
fn ctx_solver_simplify_drops_bool_redundant_disjunction() {
    // {(or p q), p} : p proves (or p q) redundant -> {p}.
    let mut s = Solver::new(Logic::QfLia);
    let p = s.declare_const("p", Sort::Bool).0;
    let q = s.declare_const("q", Sort::Bool).0;
    let clause = s.terms_mut().mk_or(vec![p, q]);

    let (out, changed) = css_apply_checked(&mut s, vec![clause, p]);
    assert!(changed);
    assert_eq!(out, vec![p], "only p should remain");
}

#[test]
fn ctx_solver_simplify_drops_valid_assertion_to_empty_goal() {
    // {(or p (not p))} : a valid assertion is redundant under the empty context
    // -> the empty goal (trivially SAT), matching z3.
    let mut s = Solver::new(Logic::QfLia);
    let p = s.declare_const("p", Sort::Bool).0;
    let np = s.terms_mut().mk_not_raw(p);
    let taut = s.terms_mut().mk_or(vec![p, np]);

    let (out, changed) = css_apply_checked(&mut s, vec![taut]);
    assert!(changed);
    assert!(
        out.is_empty(),
        "a valid-only goal simplifies to the empty goal"
    );
}

#[test]
fn ctx_solver_simplify_is_sound_identity_on_uninterpreted_goal() {
    // A goal that mentions an uninterpreted function is OUTSIDE the fragment the
    // pass replays in its sub-solver, so it is the IDENTITY (a sound no-op) —
    // even when a redundancy exists (here a duplicated assertion). This proves
    // the out-of-fragment path never silently drops a needed constraint.
    use ay_core::term::Symbol;
    let mut s = Solver::new(Logic::QfUflia);
    let x = s.declare_const("x", Sort::Int).0;
    let zero = s.int_const(0).0;
    let fx = s.terms_mut().mk_app(Symbol::named("f"), vec![x], Sort::Int);
    let atom = s
        .terms_mut()
        .mk_app(Symbol::named(">"), vec![fx, zero], Sort::Bool);

    // {(> (f x) 0), (> (f x) 0)} — a dup that the in-fragment path WOULD dedup.
    let mut goal = vec![atom, atom];
    let progressed = Tactic::CtxSolverSimplify.apply(s.terms_mut(), &mut goal);
    assert!(!progressed, "out-of-fragment goal must be a no-op");
    assert_eq!(goal, vec![atom, atom], "the goal must be left untouched");
}

/// Build a small random Bool+LIA assertion over the shared atom pool. Kept
/// shallow so the pass's cross-assertion checks stay decidable and fast.
fn css_gen_assertion(
    terms: &mut TermStore,
    atoms: &[TermId],
    rng: &mut NnfRng,
    depth: usize,
) -> TermId {
    if depth == 0 || rng.below(3) == 0 {
        return atoms[rng.below(atoms.len())];
    }
    match rng.below(4) {
        0 => {
            let a = css_gen_assertion(terms, atoms, rng, depth - 1);
            terms.mk_not_raw(a)
        }
        1 => {
            let a = css_gen_assertion(terms, atoms, rng, depth - 1);
            let b = css_gen_assertion(terms, atoms, rng, depth - 1);
            terms.mk_and(vec![a, b])
        }
        2 => {
            let a = css_gen_assertion(terms, atoms, rng, depth - 1);
            let b = css_gen_assertion(terms, atoms, rng, depth - 1);
            terms.mk_or(vec![a, b])
        }
        _ => atoms[rng.below(atoms.len())],
    }
}

#[test]
fn ctx_solver_simplify_is_equivalence_preserving_over_forty_random_goals() {
    // GOAL-PRESERVATION (the hard soundness gate): over 40 random Bool+LIA goals,
    // `input XOR ctx-solver-simplify(input)` is UNSAT — i.e. the pass is
    // equivalence-preserving (strictly stronger than the required
    // equisatisfiability, so check-sat(result) == check-sat(input) too). We also
    // record how many goals were actually simplified, to prove the pass is not a
    // no-op.
    let mut simplified = 0usize;
    let goals = 40u64;

    for seed in 0..goals {
        let mut s = Solver::new(Logic::QfLia);
        // Atom pool with deliberate implications (x=5 ⇒ x>3, x>0, …) so
        // redundancy/contradiction genuinely arise across assertions.
        let x = s.declare_const("x", Sort::Int).0;
        let y = s.declare_const("y", Sort::Int).0;
        let p = s.declare_const("p", Sort::Bool).0;
        let qb = s.declare_const("q", Sort::Bool).0;
        let mk = |t: &mut TermStore, op: &str, a: TermId, b: TermId| {
            t.mk_app(ay_core::term::Symbol::named(op), vec![a, b], Sort::Bool)
        };
        let (c0, c3, c5) = (s.int_const(0).0, s.int_const(3).0, s.int_const(5).0);
        let atoms = {
            let t = s.terms_mut();
            vec![
                p,
                qb,
                mk(t, ">", x, c3),
                mk(t, ">", x, c0),
                mk(t, "=", x, c5),
                mk(t, "<", x, c3),
                mk(t, "=", x, y),
                mk(t, "<=", y, x),
            ]
        };

        let mut rng = NnfRng::new(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15).wrapping_add(7));
        let count = 2 + rng.below(4); // 2..=5 assertions
        let mut input = Vec::with_capacity(count);
        for _ in 0..count {
            input.push(css_gen_assertion(s.terms_mut(), &atoms, &mut rng, 2));
        }

        let (_out, changed) = css_apply_checked(&mut s, input);
        if changed {
            simplified += 1;
        }
    }

    assert!(
        simplified > 0,
        "ctx-solver-simplify must actually simplify some goals (it is not a no-op)"
    );
}

#[test]
fn ctx_solver_simplify_verdict_matches_baseline_on_random_goals() {
    // Independent equisatisfiability differential: the tactic-solver verdict must
    // equal the untransformed baseline verdict on every random goal (0 mismatch).
    for seed in 0..24u64 {
        let seed_val = seed.wrapping_mul(0x9E37_79B9_7F4A_7C15).wrapping_add(11);

        // Build the same random goal in two solvers (identical seeds ⇒ identical
        // goals, since `NnfRng` is deterministic).
        let build = |s: &mut Solver, rng: &mut NnfRng| {
            let x = s.declare_const("x", Sort::Int).0;
            let y = s.declare_const("y", Sort::Int).0;
            let p = s.declare_const("p", Sort::Bool).0;
            let (c0, c3, c5) = (s.int_const(0).0, s.int_const(3).0, s.int_const(5).0);
            let mk = |t: &mut TermStore, op: &str, a: TermId, b: TermId| {
                t.mk_app(ay_core::term::Symbol::named(op), vec![a, b], Sort::Bool)
            };
            let atoms = {
                let t = s.terms_mut();
                vec![
                    p,
                    mk(t, ">", x, c3),
                    mk(t, ">", x, c0),
                    mk(t, "=", x, c5),
                    mk(t, "<", x, c3),
                    mk(t, "=", x, y),
                ]
            };
            let count = 2 + rng.below(4);
            for _ in 0..count {
                let a = css_gen_assertion(s.terms_mut(), &atoms, rng, 2);
                s.assert_term(Term(a));
            }
        };

        let mut base = Solver::new(Logic::QfLia);
        build(&mut base, &mut NnfRng::new(seed_val));
        let base_res = base.check_sat();

        let mut ts = Tactic::CtxSolverSimplify
            .solver(Logic::QfLia)
            .expect("tactic solver");
        build(ts.solver_mut(), &mut NnfRng::new(seed_val));
        let tac_res = ts.check_sat();

        assert!(!base_res.is_unknown(), "seed {seed}: baseline Unknown");
        assert!(!tac_res.is_unknown(), "seed {seed}: tactic Unknown");
        assert_eq!(
            base_res.result(),
            tac_res.result(),
            "seed {seed}: ctx-solver-simplify changed the verdict"
        );
    }
}

#[test]
fn failing_tactic_check_retires_preceding_sat_witness() {
    let mut solver = Tactic::Fail.solver(Logic::QfLia).expect("tactic solver");
    let p = solver.solver_mut().declare_const("p", Sort::Bool);
    solver.solver_mut().assert_term(p);

    // Public access to the inner solver makes a preceding ordinary result a
    // supported state, not an artificial unit-test construction.
    let preceding = solver.solver_mut().check_sat();
    assert!(preceding.is_sat());
    assert!(preceding.was_model_validated());
    assert!(solver.solver().model_for_consumer().is_some());

    let failed = solver.check_sat();

    assert!(failed.is_unknown());
    assert_eq!(
        solver.solver().unknown_reason(),
        Some(crate::UnknownReason::InternalError)
    );
    assert!(solver.solver().model().is_none());
    assert!(solver.solver().model_for_consumer().is_none());
    assert!(
        solver.inner.executor.last_result_is_unknown(),
        "the failed public query must replace the stale SAT result with registered Unknown"
    );
}

#[test]
fn failing_tactic_assuming_check_retires_witness_and_assumption_state() {
    let mut solver = Tactic::Fail.solver(Logic::QfLia).expect("tactic solver");
    let p = solver.solver_mut().declare_const("p", Sort::Bool);
    solver.solver_mut().assert_term(p);
    assert!(solver.solver_mut().check_sat().is_sat());
    assert!(solver.solver().model_for_consumer().is_some());

    let failed = solver.check_sat_assuming(&[p]);

    assert!(failed.is_unknown());
    assert_eq!(
        solver.solver().unknown_reason(),
        Some(crate::UnknownReason::InternalError)
    );
    assert!(solver.solver().model_for_consumer().is_none());
    assert!(solver.inner.last_assumptions.is_none());
    assert!(
        solver.inner.executor.last_result_is_unknown(),
        "the failed public query must replace the stale SAT result with registered Unknown"
    );
}

/// Every new transform-batch `ApplyTactic` maps to a distinct, non-`Skip`
/// executable `Tactic` with the expected name. This prevents a newly added arm
/// from silently falling through to the identity tactic.
#[test]
fn transform_batch_apply_tactics_map_to_named_non_skip_tactics() {
    let cases = [
        (ApplyTactic::ElimTermIte, "elim-term-ite"),
        (ApplyTactic::BlastTermIte, "blast-term-ite"),
        (ApplyTactic::Der, "der"),
        (ApplyTactic::DistributeForall, "distribute-forall"),
        (ApplyTactic::ReduceArgs, "reduce-args"),
    ];
    for (apply, want) in cases {
        let tac = Tactic::from_apply(&apply);
        assert_ne!(
            tac.name(),
            "skip",
            "{want} must not fall through to the Skip identity"
        );
        assert_eq!(tac.name(), want, "{want} must map to its own tactic");
    }
}
