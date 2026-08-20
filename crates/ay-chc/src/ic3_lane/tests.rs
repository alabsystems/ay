// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unit tests for the IC3 portfolio lane, including the IntBlast path that
//! lowers an unbounded `Int` counter to bit-blasted latches.

use std::sync::Arc;
use std::time::Duration;

use super::*;
use crate::clause::{ClauseBody, ClauseHead, HornClause};

fn op(o: ChcOp, args: Vec<ChcExpr>) -> ChcExpr {
    ChcExpr::Op(o, args.into_iter().map(Arc::new).collect())
}

/// Build the count-parity loop CHC over `P(acc: Bool, count: Int)`:
///   fact:       P(false, 0)
///   transition: P(acc, count) -> P(not acc, count + step)
///   query:      P(acc, count) /\ acc != (count mod 2 == 1) -> false
fn count_parity_problem(step: i128) -> ChcProblem {
    let mut p = ChcProblem::new();
    let pid = p.declare_predicate("P", vec![ChcSort::Bool, ChcSort::Int]);

    let acc = ChcVar::new("acc", ChcSort::Bool);
    let count = ChcVar::new("count", ChcSort::Int);
    let acc_e = ChcExpr::Var(acc.clone());
    let count_e = ChcExpr::Var(count.clone());

    // fact: P(false, 0)
    p.add_clause(HornClause::new(
        ClauseBody::empty(),
        ClauseHead::Predicate(pid, vec![ChcExpr::Bool(false), ChcExpr::Int(0)]),
    ));

    // transition: P(acc, count) -> P(not acc, count + step)
    let not_acc = op(ChcOp::Not, vec![acc_e.clone()]);
    let count_next = op(ChcOp::Add, vec![count_e.clone(), ChcExpr::Int(step)]);
    p.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(pid, vec![acc_e.clone(), count_e.clone()])]),
        ClauseHead::Predicate(pid, vec![not_acc, count_next]),
    ));

    // query: P(acc, count) /\ acc != (count mod 2 == 1) -> false
    let count_bit0 = op(
        ChcOp::Eq,
        vec![
            op(ChcOp::Mod, vec![count_e.clone(), ChcExpr::Int(2)]),
            ChcExpr::Int(1),
        ],
    );
    let bad = op(ChcOp::Ne, vec![acc_e.clone(), count_bit0]);
    p.add_clause(HornClause::new(
        ClauseBody::new(vec![(pid, vec![acc_e, count_e])], Some(bad)),
        ClauseHead::False,
    ));

    p
}

/// Normalise a clause to a sorted set of `(var_index, is_positive)`.
fn clause_set(clause: &[ay_sat::Literal]) -> Vec<(usize, bool)> {
    let mut v: Vec<(usize, bool)> = clause
        .iter()
        .map(|l| (l.variable().index(), l.is_positive()))
        .collect();
    v.sort_unstable();
    v.dedup();
    v
}

#[test]
fn count_parity_loop_maps_and_is_safe() {
    let problem = count_parity_problem(1);

    // The CHC must now MAP (non-None) through the IntBlast lowering.
    let lowering = lower_loop(&problem).expect("count-parity CHC should map (non-None)");

    // Layout: latch 0 = acc (Bool); latches 1..=INT_WIDTH = count bits. The bad
    // property `acc != count[0]` reads only {acc(0), count[0](1)}, and each
    // updates from itself, so the cone-of-influence slice keeps exactly those two
    // latches (count[1..] are dropped from the IC3 state set). The kept latches
    // retain their original ids 0 and 1.
    assert_eq!(lowering.ts.num_state_vars, 2);

    let mut solver = Ic3Solver::new(lowering.ts, false);
    let invariant_level = match solver.solve() {
        Ic3Result::Safe { invariant_level } => invariant_level,
        other => panic!("expected Safe from bit-level IC3, got {other:?}"),
    };

    // The synthesised invariant must contain acc <=> count[0], i.e. the two
    // clauses (!acc \/ count0) and (acc \/ !count0). acc is latch/var 0,
    // count[0] is latch/var 1.
    let clauses: Vec<_> = solver
        .invariant_clauses(invariant_level)
        .iter()
        .map(|c| clause_set(c))
        .collect();
    let want_a = vec![(0usize, false), (1usize, true)]; // !acc \/ count0
    let want_b = vec![(0usize, true), (1usize, false)]; // acc \/ !count0
    assert!(
        clauses.contains(&want_a),
        "IC3 invariant missing (!acc \\/ count0); got {clauses:?}"
    );
    assert!(
        clauses.contains(&want_b),
        "IC3 invariant missing (acc \\/ !count0); got {clauses:?}"
    );
}

#[test]
fn count_parity_loop_back_translates_to_candidate() {
    let problem = count_parity_problem(1);
    // The full lane returns a non-None candidate invariant model on Safe.
    let model = try_prove_chc_loop(&problem, Duration::from_secs(5));
    assert!(
        model.is_some(),
        "lane should produce a candidate invariant model"
    );
}

#[test]
fn count_parity_loop_zero_timeout_returns_none_promptly() {
    // The previously-ignored timeout is now honored: a zero/expired budget makes
    // IC3 stop at its first loop head and return Unknown, which the lane maps to
    // "no candidate" (None) -- sound, and no longer an unbounded spin. Contrast
    // count_parity_loop_back_translates_to_candidate, which proves Safe at 5s.
    let problem = count_parity_problem(1);
    let start = std::time::Instant::now();
    let res = try_prove_chc_loop(&problem, Duration::from_nanos(0));
    assert!(
        res.is_none(),
        "an expired timeout must yield no candidate, not a proof"
    );
    assert!(
        start.elapsed() < Duration::from_secs(2),
        "the deadline must be honored promptly, not spun through"
    );
}

// ---------------------------------------------------------------------------
// Real-shaped lowering: a multi-block BitVec(64) CFG (one relation per basic
// block) for the count-parity loop, mirroring the targo-lowered shape (7
// relations, BitVec(64) state, `BvAdd`/`BvAnd` ops). The lane must (a) linearize
// the CFG to one recursive predicate, (b) bit-blast the BitVec(64) args, and
// (c) encode the Bv* ops, then the bit-level IC3 must find acc <=> count[0].
// ---------------------------------------------------------------------------

/// `count[0] == 1`, i.e. `(bvand count 1) == 1` over BitVec(64).
fn bv64_parity(count_e: &ChcExpr) -> ChcExpr {
    let one = ChcExpr::BitVec(1, 64);
    let lo = op(ChcOp::BvAnd, vec![count_e.clone(), one.clone()]);
    op(ChcOp::Eq, vec![lo, one])
}

/// Build the REAL-shaped 7-relation count-parity CHC:
///   bb0(acc,count): entry         true        -> bb0(false, 0)
///   bb1 = loop header             bb0(s)      -> bb1(s)
///   bb2 = post-assert (guarded)   bb1(s) /\ acc==count[0] -> bb2(s)
///   error (query)                 bb1(s) /\ acc!=count[0] -> false
///   bb3 = acc := not acc          bb2(s)      -> bb3(not acc, count)
///   bb4 = count := count + step   bb3(s)      -> bb4(acc, count + step)
///   bb5 = back edge               bb4(s)      -> bb5(s)
///                                 bb5(s)      -> bb1(s)
/// Relations: bb0..bb5 (6) + the error query = 7. Loop SCC = {bb1..bb5}.
/// All state is `(acc: Bool, count: BitVec(64))`; `step` is a BitVec(64) const.
fn bv64_count_parity_cfg(step: u128) -> ChcProblem {
    let mut p = ChcProblem::new();
    let sorts = vec![ChcSort::Bool, ChcSort::BitVec(64)];
    let bb0 = p.declare_predicate("bb0", sorts.clone());
    let bb1 = p.declare_predicate("bb1", sorts.clone());
    let bb2 = p.declare_predicate("bb2", sorts.clone());
    let bb3 = p.declare_predicate("bb3", sorts.clone());
    let bb4 = p.declare_predicate("bb4", sorts.clone());
    let bb5 = p.declare_predicate("bb5", sorts.clone());

    let acc = ChcVar::new("acc", ChcSort::Bool);
    let count = ChcVar::new("count", ChcSort::BitVec(64));
    let acc_e = ChcExpr::Var(acc.clone());
    let count_e = ChcExpr::Var(count.clone());
    let state = || vec![acc_e.clone(), count_e.clone()];

    // entry fact: bb0(false, 0)
    p.add_clause(HornClause::new(
        ClauseBody::empty(),
        ClauseHead::Predicate(bb0, vec![ChcExpr::Bool(false), ChcExpr::BitVec(0, 64)]),
    ));
    // bb0 -> bb1
    p.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(bb0, state())]),
        ClauseHead::Predicate(bb1, state()),
    ));
    // bb1 /\ acc == count[0] -> bb2  (assert holds, continue)
    let assert_ok = op(ChcOp::Eq, vec![acc_e.clone(), bv64_parity(&count_e)]);
    p.add_clause(HornClause::new(
        ClauseBody::new(vec![(bb1, state())], Some(assert_ok)),
        ClauseHead::Predicate(bb2, state()),
    ));
    // bb1 /\ acc != count[0] -> false  (assert fails, panic)
    let assert_bad = op(ChcOp::Ne, vec![acc_e.clone(), bv64_parity(&count_e)]);
    p.add_clause(HornClause::new(
        ClauseBody::new(vec![(bb1, state())], Some(assert_bad)),
        ClauseHead::False,
    ));
    // bb2 -> bb3(not acc, count)
    let not_acc = op(ChcOp::Not, vec![acc_e.clone()]);
    p.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(bb2, state())]),
        ClauseHead::Predicate(bb3, vec![not_acc, count_e.clone()]),
    ));
    // bb3 -> bb4(acc, count + step)
    let count_next = op(
        ChcOp::BvAdd,
        vec![count_e.clone(), ChcExpr::BitVec(step, 64)],
    );
    p.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(bb3, state())]),
        ClauseHead::Predicate(bb4, vec![acc_e.clone(), count_next]),
    ));
    // bb4 -> bb5 -> bb1
    p.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(bb4, state())]),
        ClauseHead::Predicate(bb5, state()),
    ));
    p.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(bb5, state())]),
        ClauseHead::Predicate(bb1, state()),
    ));

    p
}

#[test]
fn bv64_cfg_linearizes_to_single_recursive_predicate() {
    let problem = bv64_count_parity_cfg(1);
    assert_eq!(problem.predicates().len(), 6, "bb0..bb5");

    // (a) The 7-relation CFG collapses to ONE recursive predicate.
    let (linear, _header) = linearize_to_single_loop(&problem)
        .expect("multi-block BitVec CFG should linearize to one recursive predicate");
    assert_eq!(
        linear.predicates().len(),
        1,
        "linearized to a single predicate"
    );

    // The collapsed problem must have a fact, a self-loop transition, and a
    // query over the single predicate.
    let pid = linear.predicates()[0].id;
    let mut facts = 0;
    let mut transitions = 0;
    let mut queries = 0;
    for c in linear.clauses() {
        match &c.head {
            crate::clause::ClauseHead::Predicate(h, _) if *h == pid => {
                if c.body.predicates.is_empty() {
                    facts += 1;
                } else {
                    transitions += 1;
                }
            }
            crate::clause::ClauseHead::False => queries += 1,
            _ => {}
        }
    }
    assert_eq!(facts, 1, "one entry fact");
    assert_eq!(transitions, 1, "one composed loop transition");
    assert!(queries >= 1, "at least one error query");
}

#[test]
fn bv64_cfg_maps_and_ic3_finds_acc_iff_count0() {
    let problem = bv64_count_parity_cfg(1);

    // (a)+(b)+(c): the REAL-shaped 7-relation BitVec(64) CHC MAPS through the
    // linearize -> bit-blast -> Bv-op-encode lowering.
    let lowering =
        lower_loop(&problem).expect("7-relation BitVec(64) count-parity CHC should map (non-None)");

    // Layout: latch 0 = acc (Bool); latch 1 = count[0]. The bad property
    // `(bvand count 1) == 1` is constant-folded during bit-blasting — each high
    // bit is `count[i] & 0 = 0` with NO fan-in to `count[i]` — so the
    // cone-of-influence keeps ONLY {acc, count[0]} (2 latches), giving IC3 the
    // tight `acc <=> count[0]` invariant directly (a giant multi-bit CNF would
    // otherwise overwhelm the trusted word-level re-validator).
    assert_eq!(lowering.ts.num_state_vars, 2);

    let mut solver = Ic3Solver::new(lowering.ts, false);
    let invariant_level = match solver.solve() {
        Ic3Result::Safe { invariant_level } => invariant_level,
        other => panic!("expected Safe from bit-level IC3 on BitVec(64) CFG, got {other:?}"),
    };

    // The synthesised invariant must contain acc <=> count[0] (acc = var 0,
    // count[0] = var 1): clauses (!acc \/ count0) and (acc \/ !count0).
    let clauses: Vec<_> = solver
        .invariant_clauses(invariant_level)
        .iter()
        .map(|c| clause_set(c))
        .collect();
    let want_a = vec![(0usize, false), (1usize, true)];
    let want_b = vec![(0usize, true), (1usize, false)];
    assert!(
        clauses.contains(&want_a),
        "IC3 invariant missing (!acc \\/ count0); got {clauses:?}"
    );
    assert!(
        clauses.contains(&want_b),
        "IC3 invariant missing (acc \\/ !count0); got {clauses:?}"
    );

    // Full lane returns a back-translated candidate model.
    assert!(
        try_prove_chc_loop(&problem, Duration::from_secs(10)).is_some(),
        "lane should produce a candidate invariant model for the BitVec(64) CFG"
    );
}

#[test]
fn bv64_false_parity_cfg_is_not_safe() {
    // step = 2: count[0] never changes while acc toggles, so acc != count[0]
    // is reachable. Maps, but the bit-level engine must NOT report Safe.
    let problem = bv64_count_parity_cfg(2);
    let lowering = lower_loop(&problem).expect("false-parity BitVec(64) CFG should still map");
    let mut solver = Ic3Solver::new(lowering.ts, false);
    assert!(
        !matches!(solver.solve(), Ic3Result::Safe { .. }),
        "false-parity BitVec(64) CFG must not be proven Safe"
    );
    assert!(try_prove_chc_loop(&problem, Duration::from_secs(10)).is_none());
}

// ---------------------------------------------------------------------------
// Dead block-state args: the cone-of-influence slice. A real targo-lowered loop
// header carries EVERY block-live variable as an argument; most do not feed the
// asserted property. We model that with a single recursive predicate whose
// header carries the parity state PLUS several dead `Int` "block-state" args that
// evolve (mixing bits via `+`) but never influence `acc`/`count`. Without the
// slice IC3 must generalise/propagate over all 1 + (1+ndead)*INT_WIDTH latches
// and does not converge; the COI slice prunes to {acc, count[0]} so IC3 finds
// `acc <=> count[0]` immediately. SOUND: the dropped latches are only freed.
// ---------------------------------------------------------------------------

/// Count-parity loop whose header also carries `ndead` dead `Int` block-state
/// args `d0..d{ndead-1}` updated by `d0' = d0 + count`, `d_k' = d_k + d_{k-1}`
/// (bit-mixing, so each is a wide live latch), none of which the bad property
/// reads. `step` is the counter increment.
fn dead_block_state_problem(step: i128, ndead: usize) -> ChcProblem {
    let mut p = ChcProblem::new();
    let mut sorts = vec![ChcSort::Bool, ChcSort::Int];
    for _ in 0..ndead {
        sorts.push(ChcSort::Int);
    }
    let pid = p.declare_predicate("P", sorts);

    let acc = ChcVar::new("acc", ChcSort::Bool);
    let count = ChcVar::new("count", ChcSort::Int);
    let acc_e = ChcExpr::Var(acc);
    let count_e = ChcExpr::Var(count);
    let dead: Vec<ChcExpr> = (0..ndead)
        .map(|k| ChcExpr::Var(ChcVar::new(format!("d{k}"), ChcSort::Int)))
        .collect();

    // fact: P(false, 0, 0, ..., 0)
    let mut fact_args = vec![ChcExpr::Bool(false), ChcExpr::Int(0)];
    for _ in 0..ndead {
        fact_args.push(ChcExpr::Int(0));
    }
    p.add_clause(HornClause::new(
        ClauseBody::empty(),
        ClauseHead::Predicate(pid, fact_args),
    ));

    // transition: dead args mix bits but never feed acc/count.
    let mut in_args = vec![acc_e.clone(), count_e.clone()];
    in_args.extend(dead.iter().cloned());
    let mut out_args = vec![
        op(ChcOp::Not, vec![acc_e.clone()]),
        op(ChcOp::Add, vec![count_e.clone(), ChcExpr::Int(step)]),
    ];
    for k in 0..ndead {
        let prev = if k == 0 {
            count_e.clone()
        } else {
            dead[k - 1].clone()
        };
        out_args.push(op(ChcOp::Add, vec![dead[k].clone(), prev]));
    }
    p.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(pid, in_args)]),
        ClauseHead::Predicate(pid, out_args),
    ));

    // query: P(...) /\ acc != (count mod 2 == 1) -> false
    let count_bit0 = op(
        ChcOp::Eq,
        vec![
            op(ChcOp::Mod, vec![count_e.clone(), ChcExpr::Int(2)]),
            ChcExpr::Int(1),
        ],
    );
    let bad = op(ChcOp::Ne, vec![acc_e.clone(), count_bit0]);
    let mut q_args = vec![acc_e, count_e];
    q_args.extend(dead);
    p.add_clause(HornClause::new(
        ClauseBody::new(vec![(pid, q_args)], Some(bad)),
        ClauseHead::False,
    ));
    p
}

#[test]
fn dead_block_state_args_slice_to_parity_coi() {
    let ndead = 4;
    let problem = dead_block_state_problem(1, ndead);

    // Full latch count without slicing: acc(1) + (1 + ndead) Int args * INT_WIDTH.
    let full = 1 + (1 + ndead) * INT_WIDTH;
    assert!(full > 5 * INT_WIDTH, "header should be wide");

    let lowering = lower_loop(&problem).expect("dead-arg count-parity CHC should map");
    // COI slice keeps only {acc(0), count[0](1)}.
    assert_eq!(
        lowering.ts.num_state_vars, 2,
        "cone-of-influence must prune dead block-state to {{acc, count[0]}}"
    );

    let mut solver = Ic3Solver::new(lowering.ts, false);
    let invariant_level = match solver.solve() {
        Ic3Result::Safe { invariant_level } => invariant_level,
        other => panic!("sliced IC3 should be Safe, got {other:?}"),
    };
    let clauses: Vec<_> = solver
        .invariant_clauses(invariant_level)
        .iter()
        .map(|c| clause_set(c))
        .collect();
    assert!(
        clauses.contains(&vec![(0usize, false), (1usize, true)]),
        "missing !acc\\/count0: {clauses:?}"
    );
    assert!(
        clauses.contains(&vec![(0usize, true), (1usize, false)]),
        "missing acc\\/!count0: {clauses:?}"
    );

    assert!(
        try_prove_chc_loop(&problem, Duration::from_secs(10)).is_some(),
        "lane should produce a candidate for the dead-arg loop"
    );
}

#[test]
fn dead_block_state_args_false_is_not_safe() {
    // step = 2: count[0] pinned to 0 while acc toggles -> reachably bad. The slice
    // keeps {acc, count[0]} and IC3 must still find the counterexample.
    let problem = dead_block_state_problem(2, 4);
    let lowering = lower_loop(&problem).expect("should map");
    assert_eq!(lowering.ts.num_state_vars, 2);
    let mut solver = Ic3Solver::new(lowering.ts, false);
    assert!(
        !matches!(solver.solve(), Ic3Result::Safe { .. }),
        "false dead-arg parity loop must not be Safe"
    );
    assert!(try_prove_chc_loop(&problem, Duration::from_secs(10)).is_none());
}

#[test]
fn bv64_cfg_candidate_validates_against_original_multi_pred_problem() {
    // End-to-end: the lane must produce a candidate model keyed on the ORIGINAL
    // 6 block predicates (not the collapsed predicate) that the UNCHANGED
    // word-level validator accepts against the original multi-predicate problem.
    let problem = bv64_count_parity_cfg(1);
    let model = try_prove_chc_loop(&problem, Duration::from_secs(30))
        .expect("lane should produce a candidate for the BitVec(64) CFG");
    // The lifted model must cover every original predicate.
    assert_eq!(
        model.len(),
        problem.predicates().len(),
        "model covers all blocks"
    );
    for pred in problem.predicates() {
        assert!(model.get(&pred.id).is_some(), "interp for {}", pred.name);
    }
    // The trusted validator must ACCEPT it on the original transition.
    let ok = crate::engines::validate_external_invariant_model(
        &problem,
        &model,
        &crate::PdrConfig::production(false),
    )
    .expect("validation should not error");
    assert!(
        ok,
        "lifted candidate must re-validate on the original multi-pred problem"
    );
}

#[test]
fn bv64_false_cfg_lift_does_not_validate() {
    // The false-parity CFG (step=2) must NOT yield a validating model: the
    // bit-level engine refuses Safe, so the lane returns no candidate at all.
    let problem = bv64_count_parity_cfg(2);
    assert!(
        try_prove_chc_loop(&problem, Duration::from_secs(30)).is_none(),
        "false-parity CFG must not produce a (validating) candidate"
    );
}

/// Build the REAL targo-lowered SSA shape (from the live TRUST_IC3_LANE_DEBUG
/// dump): WIDE block predicates carrying threaded SSA temps, count threaded
/// through SHIFTING arg positions, acc' encoded as a boolean `Ite` select, and
/// an explicit arity-0 `error` query predicate. This is the shape that the clean
/// arity-2 `bv64_count_parity_cfg` does NOT exercise.
///   bb0[Bool,BV64]; bb1[Bool,BV64,BV64,Bool,BV64] (p3=acc,p4=count,p0..2 temps);
///   bb2[Bool,BV64,Bool,BV64] (p2=acc,p3=count); bb3/bb4 like bb1; error[] (bad).
fn bv64_real_ssa_cfg(step: u128) -> ChcProblem {
    let mut p = ChcProblem::new();
    let w = |n| ChcSort::BitVec(n);
    let s5 = vec![ChcSort::Bool, w(64), w(64), ChcSort::Bool, w(64)];
    let s4 = vec![ChcSort::Bool, w(64), ChcSort::Bool, w(64)];
    let bb0 = p.declare_predicate("bb0", vec![ChcSort::Bool, w(64)]);
    let bb1 = p.declare_predicate("bb1", s5.clone());
    let bb2 = p.declare_predicate("bb2", s4.clone());
    let bb3 = p.declare_predicate("bb3", s5.clone());
    let bb4 = p.declare_predicate("bb4", s5.clone());
    let error = p.declare_predicate("error", vec![]);

    let v = |n: &str, s: ChcSort| ChcExpr::Var(ChcVar::new(n, s));
    let parity = |c: &ChcExpr| {
        op(
            ChcOp::Eq,
            vec![
                op(ChcOp::BvAnd, vec![c.clone(), ChcExpr::BitVec(1, 64)]),
                ChcExpr::BitVec(1, 64),
            ],
        )
    };

    // [0] bb0(c13,c15) :- true
    p.add_clause(HornClause::new(
        ClauseBody::empty(),
        ClauseHead::Predicate(bb0, vec![v("c13", ChcSort::Bool), v("c15", w(64))]),
    ));
    // [1] enter: bb1(undef0,undef2,v39,false,0) :- bb0(c13,c15)
    p.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(bb0, vec![v("c13", ChcSort::Bool), v("c15", w(64))])]),
        ClauseHead::Predicate(
            bb1,
            vec![
                v("u0", ChcSort::Bool),
                v("u2", w(64)),
                v("v39", w(64)),
                ChcExpr::Bool(false),
                ChcExpr::BitVec(0, 64),
            ],
        ),
    ));
    let bb1_body = || {
        (
            bb1,
            vec![
                v("t12", ChcSort::Bool),
                v("t14", w(64)),
                v("t39", w(64)),
                v("c13", ChcSort::Bool),
                v("c15", w(64)),
            ],
        )
    };
    let c13 = v("c13", ChcSort::Bool);
    let c15 = v("c15", w(64));
    // [2] assert-FAIL: bb3(t12,t14,t39,c13,c15) :- bb1(..), Not(c13 == count[0])
    p.add_clause(HornClause::new(
        ClauseBody::new(
            vec![bb1_body()],
            Some(op(
                ChcOp::Not,
                vec![op(ChcOp::Eq, vec![c13.clone(), parity(&c15)])],
            )),
        ),
        ClauseHead::Predicate(
            bb3,
            vec![
                v("t12", ChcSort::Bool),
                v("t14", w(64)),
                v("t39", w(64)),
                c13.clone(),
                c15.clone(),
            ],
        ),
    ));
    // [3] assert-OK: bb2(t12,t14,c13,c15) :- bb1(..), (c13 == count[0])   [t39 body-only]
    p.add_clause(HornClause::new(
        ClauseBody::new(
            vec![bb1_body()],
            Some(op(ChcOp::Eq, vec![c13.clone(), parity(&c15)])),
        ),
        ClauseHead::Predicate(
            bb2,
            vec![
                v("t12", ChcSort::Bool),
                v("t14", w(64)),
                c13.clone(),
                c15.clone(),
            ],
        ),
    ));
    // [4] update: bb4(t12,t14, count+step, Ite(c13,false,true)=!acc, c15) :- bb2(t12,t14,c13,c15)
    let acc_next = op(
        ChcOp::Ite,
        vec![
            c13.clone(),
            op(ChcOp::Not, vec![ChcExpr::Bool(true)]),
            ChcExpr::Bool(true),
        ],
    );
    let count_next = op(ChcOp::BvAdd, vec![c15.clone(), ChcExpr::BitVec(step, 64)]);
    p.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(
            bb2,
            vec![
                v("t12", ChcSort::Bool),
                v("t14", w(64)),
                c13.clone(),
                c15.clone(),
            ],
        )]),
        ClauseHead::Predicate(
            bb4,
            vec![
                v("t12", ChcSort::Bool),
                v("t14", w(64)),
                count_next,
                acc_next,
                c15.clone(),
            ],
        ),
    ));
    // [5] error() :- bb3(t12,t14,t39,c13,c15)
    p.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(
            bb3,
            vec![
                v("t12", ChcSort::Bool),
                v("t14", w(64)),
                v("t39", w(64)),
                c13.clone(),
                c15.clone(),
            ],
        )]),
        ClauseHead::Predicate(error, vec![]),
    ));
    // [7] loop back: bb1(t12,t14,t39,c13, t39) :- bb4(t12,t14,t39,c13,c15)   [count := pos2=t39]
    p.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(
            bb4,
            vec![
                v("t12", ChcSort::Bool),
                v("t14", w(64)),
                v("t39", w(64)),
                c13.clone(),
                c15.clone(),
            ],
        )]),
        ClauseHead::Predicate(
            bb1,
            vec![
                v("t12", ChcSort::Bool),
                v("t14", w(64)),
                v("t39", w(64)),
                c13.clone(),
                v("t39", w(64)),
            ],
        ),
    ));
    // [8] false :- error()
    p.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(error, vec![])]),
        ClauseHead::False,
    ));
    p
}

#[test]
fn bv64_real_ssa_cfg_validates() {
    let problem = bv64_real_ssa_cfg(1);
    assert!(
        lower_loop(&problem).is_some(),
        "real SSA CFG should map/linearize"
    );
    let model = try_prove_chc_loop(&problem, Duration::from_secs(30))
        .expect("lane should produce a candidate for the real SSA CFG");
    assert_eq!(
        model.len(),
        problem.predicates().len(),
        "model covers all blocks"
    );
    let ok = crate::engines::validate_external_invariant_model(
        &problem,
        &model,
        &crate::PdrConfig::production(false),
    )
    .expect("validation should not error");
    assert!(
        ok,
        "lifted candidate must re-validate on the real SSA multi-pred problem"
    );
}

#[test]
fn bv64_real_ssa_cfg_false_not_safe() {
    // step=2: parity pinned, acc toggles -> bad reachable. Must NOT validate.
    let problem = bv64_real_ssa_cfg(2);
    assert!(
        try_prove_chc_loop(&problem, Duration::from_secs(30)).is_none(),
        "false real-SSA CFG must not produce a validating candidate"
    );
}

#[test]
fn false_parity_loop_is_not_safe() {
    // step = 2: count parity never changes but acc toggles, so acc != count[0]
    // is reachable. The bit-level engine must NOT report Safe, so the lane
    // produces no candidate (soundness at the bit level; the kernel re-check is
    // the ultimate gate).
    let problem = count_parity_problem(2);
    let lowering = lower_loop(&problem).expect("should still map");
    let mut solver = Ic3Solver::new(lowering.ts, false);
    assert!(
        !matches!(solver.solve(), Ic3Result::Safe { .. }),
        "false-parity loop must not be proven Safe"
    );
    assert!(try_prove_chc_loop(&problem, Duration::from_secs(5)).is_none());
}

/// EXACT reconstruction of obl2-dump.txt (the real 7-pred/16-clause thread-split
/// obligation the lane receives). Used only by `diag_real_obl2` to ground-truth
/// the lane's behavior on the real dumped problem.
fn real_obl2_thread_split() -> ChcProblem {
    let mut p = ChcProblem::new();
    let w = |n| ChcSort::BitVec(n);
    let st = vec![ChcSort::Bool, w(64)];
    let bb0 = p.declare_predicate("bb0", vec![]);
    let bb1 = p.declare_predicate("bb1", st.clone());
    let bb2 = p.declare_predicate("bb2", st.clone());
    let bb3 = p.declare_predicate("bb3", st.clone());
    let bb4 = p.declare_predicate("bb4", st.clone());
    let bb5 = p.declare_predicate("bb5", st.clone());
    let error = p.declare_predicate("error", vec![]);

    let vb = |n: &str| ChcExpr::Var(ChcVar::new(n, ChcSort::Bool));
    let vv = |n: &str| ChcExpr::Var(ChcVar::new(n, w(64)));
    // assert condition: load6 == ((load7 & 1) == 1)  [load6/load7 are FREE temps]
    let assert_eq = || {
        op(
            ChcOp::Eq,
            vec![
                vb("load6"),
                op(
                    ChcOp::Eq,
                    vec![
                        op(ChcOp::BvAnd, vec![vv("load7"), ChcExpr::BitVec(1, 64)]),
                        ChcExpr::BitVec(1, 64),
                    ],
                ),
            ],
        )
    };
    let thr = |b: &str| vec![vb(&format!("{b}_v13")), vv(&format!("{b}_v15"))];

    // [0] bb0() :- .
    p.add_clause(HornClause::new(
        ClauseBody::empty(),
        ClauseHead::Predicate(bb0, vec![]),
    ));
    // [1] bb1(undef0, undef3) :- bb0()
    p.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(bb0, vec![])]),
        ClauseHead::Predicate(bb1, vec![vb("undef0"), vv("undef3")]),
    ));
    // [2],[3] error() :- bb1(v13,v15) /\ true   (unsupported-instruction fail-closed edges)
    for _ in 0..2 {
        p.add_clause(HornClause::new(
            ClauseBody::new(vec![(bb1, thr("bb1"))], Some(ChcExpr::Bool(true))),
            ClauseHead::Predicate(error, vec![]),
        ));
    }
    // [4] bb3(v13,v15) :- bb1(v13,v15) /\ Not(assert)
    p.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(bb1, thr("bb1"))],
            Some(op(ChcOp::Not, vec![assert_eq()])),
        ),
        ClauseHead::Predicate(bb3, thr("bb1")),
    ));
    // [5] bb2(v13,v15) :- bb1(v13,v15) /\ assert
    p.add_clause(HornClause::new(
        ClauseBody::new(vec![(bb1, thr("bb1"))], Some(assert_eq())),
        ClauseHead::Predicate(bb2, thr("bb1")),
    ));
    // [6] error() :- bb2 /\ true
    p.add_clause(HornClause::new(
        ClauseBody::new(vec![(bb2, thr("bb2"))], Some(ChcExpr::Bool(true))),
        ClauseHead::Predicate(error, vec![]),
    ));
    // [7] bb4(v13,v15) :- bb2(v13,v15)
    p.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(bb2, thr("bb2"))]),
        ClauseHead::Predicate(bb4, thr("bb2")),
    ));
    // [8],[9] error() :- bb3 /\ true
    for _ in 0..2 {
        p.add_clause(HornClause::new(
            ClauseBody::new(vec![(bb3, thr("bb3"))], Some(ChcExpr::Bool(true))),
            ClauseHead::Predicate(error, vec![]),
        ));
    }
    // [10],[11] error() :- bb4 /\ true
    for _ in 0..2 {
        p.add_clause(HornClause::new(
            ClauseBody::new(vec![(bb4, thr("bb4"))], Some(ChcExpr::Bool(true))),
            ClauseHead::Predicate(error, vec![]),
        ));
    }
    // [12] bb5(v13,v15) :- bb4(v13,v15)
    p.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(bb4, thr("bb4"))]),
        ClauseHead::Predicate(bb5, thr("bb4")),
    ));
    // [13] error() :- bb5 /\ true
    p.add_clause(HornClause::new(
        ClauseBody::new(vec![(bb5, thr("bb5"))], Some(ChcExpr::Bool(true))),
        ClauseHead::Predicate(error, vec![]),
    ));
    // [14] bb1(v13,v15) :- bb5(v13,v15)   (back-edge, identity)
    p.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(bb5, thr("bb5"))]),
        ClauseHead::Predicate(bb1, thr("bb5")),
    ));
    // [15] false :- error()
    p.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(error, vec![])]),
        ClauseHead::False,
    ));
    p
}

/// Single-predicate count-parity loop where the assert reads LOADED TEMPS
/// (`la == acc`, `lc == count`) instead of the header args directly — the
/// SSA/mem shape where a loop-head assert loads the mutable cells into temps.
/// `la`/`lc` are clause-local; without resolving them to the header args the
/// `lc == count` link drags EVERY count bit into `bad`'s cone (coi stays wide,
/// IC3 cannot converge). Resolving the temps to args collapses `bad` to
/// `Not(acc == (count&1==1))` → coi {acc,count[0]}.
fn bv_temp_chain_parity_problem(step: u128) -> ChcProblem {
    let mut p = ChcProblem::new();
    let w = |n| ChcSort::BitVec(n);
    let pid = p.declare_predicate("P", vec![ChcSort::Bool, w(64)]);
    let acc = ChcExpr::Var(ChcVar::new("acc", ChcSort::Bool));
    let count = ChcExpr::Var(ChcVar::new("count", w(64)));
    let la = ChcExpr::Var(ChcVar::new("la", ChcSort::Bool));
    let lc = ChcExpr::Var(ChcVar::new("lc", w(64)));
    // fact P(false, 0)
    p.add_clause(HornClause::new(
        ClauseBody::empty(),
        ClauseHead::Predicate(pid, vec![ChcExpr::Bool(false), ChcExpr::BitVec(0, 64)]),
    ));
    // transition P(acc,count) -> P(!acc, count+step)
    let not_acc = op(ChcOp::Not, vec![acc.clone()]);
    let count_next = op(ChcOp::BvAdd, vec![count.clone(), ChcExpr::BitVec(step, 64)]);
    p.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(pid, vec![acc.clone(), count.clone()])]),
        ClauseHead::Predicate(pid, vec![not_acc, count_next]),
    ));
    // query: P(acc,count) /\ la==acc /\ lc==count /\ Not(la == (lc&1==1)) -> false
    let parity_lc = op(
        ChcOp::Eq,
        vec![
            op(ChcOp::BvAnd, vec![lc.clone(), ChcExpr::BitVec(1, 64)]),
            ChcExpr::BitVec(1, 64),
        ],
    );
    let bad = op(
        ChcOp::And,
        vec![
            op(ChcOp::Eq, vec![la.clone(), acc.clone()]),
            op(ChcOp::Eq, vec![lc.clone(), count.clone()]),
            op(ChcOp::Not, vec![op(ChcOp::Eq, vec![la.clone(), parity_lc])]),
        ],
    );
    p.add_clause(HornClause::new(
        ClauseBody::new(vec![(pid, vec![acc.clone(), count.clone()])], Some(bad)),
        ClauseHead::False,
    ));
    p
}

/// `bv64_real_ssa_cfg` but with the accumulator update in the REAL summarized-call
/// shape `Ite(true, Not(acc), acc)` (a CONSTANT-condition `Select`, as the genuine
/// `a ^ b` lowers with `b = true`) rather than the hand-written invertible
/// `Ite(acc, false, true)`. `invert_head_arg` cannot invert a const-cond `Ite`
/// until it is folded, so the lift fails without the Gap-C const-fold.
fn bv64_real_ssa_cfg_constite(step: u128) -> ChcProblem {
    let mut p = ChcProblem::new();
    let w = |n| ChcSort::BitVec(n);
    let s5 = vec![ChcSort::Bool, w(64), w(64), ChcSort::Bool, w(64)];
    let s4 = vec![ChcSort::Bool, w(64), ChcSort::Bool, w(64)];
    let bb0 = p.declare_predicate("bb0", vec![ChcSort::Bool, w(64)]);
    let bb1 = p.declare_predicate("bb1", s5.clone());
    let bb2 = p.declare_predicate("bb2", s4.clone());
    let bb3 = p.declare_predicate("bb3", s5.clone());
    let bb4 = p.declare_predicate("bb4", s5.clone());
    let error = p.declare_predicate("error", vec![]);
    let v = |n: &str, s: ChcSort| ChcExpr::Var(ChcVar::new(n, s));
    let parity = |c: &ChcExpr| {
        op(
            ChcOp::Eq,
            vec![
                op(ChcOp::BvAnd, vec![c.clone(), ChcExpr::BitVec(1, 64)]),
                ChcExpr::BitVec(1, 64),
            ],
        )
    };
    p.add_clause(HornClause::new(
        ClauseBody::empty(),
        ClauseHead::Predicate(bb0, vec![v("c13", ChcSort::Bool), v("c15", w(64))]),
    ));
    p.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(bb0, vec![v("c13", ChcSort::Bool), v("c15", w(64))])]),
        ClauseHead::Predicate(
            bb1,
            vec![
                v("u0", ChcSort::Bool),
                v("u2", w(64)),
                v("v39", w(64)),
                ChcExpr::Bool(false),
                ChcExpr::BitVec(0, 64),
            ],
        ),
    ));
    let bb1_body = || {
        (
            bb1,
            vec![
                v("t12", ChcSort::Bool),
                v("t14", w(64)),
                v("t39", w(64)),
                v("c13", ChcSort::Bool),
                v("c15", w(64)),
            ],
        )
    };
    let c13 = v("c13", ChcSort::Bool);
    let c15 = v("c15", w(64));
    p.add_clause(HornClause::new(
        ClauseBody::new(
            vec![bb1_body()],
            Some(op(
                ChcOp::Not,
                vec![op(ChcOp::Eq, vec![c13.clone(), parity(&c15)])],
            )),
        ),
        ClauseHead::Predicate(
            bb3,
            vec![
                v("t12", ChcSort::Bool),
                v("t14", w(64)),
                v("t39", w(64)),
                c13.clone(),
                c15.clone(),
            ],
        ),
    ));
    p.add_clause(HornClause::new(
        ClauseBody::new(
            vec![bb1_body()],
            Some(op(ChcOp::Eq, vec![c13.clone(), parity(&c15)])),
        ),
        ClauseHead::Predicate(
            bb2,
            vec![
                v("t12", ChcSort::Bool),
                v("t14", w(64)),
                c13.clone(),
                c15.clone(),
            ],
        ),
    ));
    // acc' = Ite(true, Not(acc), acc)  (const-condition Select from the real call)
    let acc_next = op(
        ChcOp::Ite,
        vec![
            ChcExpr::Bool(true),
            op(ChcOp::Not, vec![c13.clone()]),
            c13.clone(),
        ],
    );
    let count_next = op(ChcOp::BvAdd, vec![c15.clone(), ChcExpr::BitVec(step, 64)]);
    p.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(
            bb2,
            vec![
                v("t12", ChcSort::Bool),
                v("t14", w(64)),
                c13.clone(),
                c15.clone(),
            ],
        )]),
        ClauseHead::Predicate(
            bb4,
            vec![
                v("t12", ChcSort::Bool),
                v("t14", w(64)),
                count_next,
                acc_next,
                c15.clone(),
            ],
        ),
    ));
    p.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(
            bb3,
            vec![
                v("t12", ChcSort::Bool),
                v("t14", w(64)),
                v("t39", w(64)),
                c13.clone(),
                c15.clone(),
            ],
        )]),
        ClauseHead::Predicate(error, vec![]),
    ));
    p.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(
            bb4,
            vec![
                v("t12", ChcSort::Bool),
                v("t14", w(64)),
                v("t39", w(64)),
                c13.clone(),
                c15.clone(),
            ],
        )]),
        ClauseHead::Predicate(
            bb1,
            vec![
                v("t12", ChcSort::Bool),
                v("t14", w(64)),
                v("t39", w(64)),
                c13.clone(),
                v("t39", w(64)),
            ],
        ),
    ));
    p.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(error, vec![])]),
        ClauseHead::False,
    ));
    p
}

fn validates(p: &ChcProblem) -> bool {
    match try_prove_chc_loop(p, Duration::from_secs(20)) {
        Some(model) => crate::engines::validate_external_invariant_model(
            p,
            &model,
            &crate::PdrConfig::production(false),
        )
        .unwrap_or(false),
        None => false,
    }
}

// --- Gap B: query assert-temp-chain resolves to header-arg latches -----------

#[test]
fn temp_chain_query_resolves_to_arg_coi_and_validates() {
    // The assert reads loaded temps (`la == acc`, `lc == count`) rather than the
    // header args. WITHOUT resolving them, the `lc == count` link drags EVERY count
    // bit into `bad`'s cone (coi 9->9, no slice). The Gap-B one-point elimination in
    // the query lowering rewrites the temps back onto {acc, count}, collapsing `bad`
    // to `Not(acc == (count&1==1))` so the cone-of-influence keeps exactly
    // {acc, count[0]} (2 latches) and IC3 finds `acc <=> count[0]`.
    let problem = bv_temp_chain_parity_problem(1);
    let lowering = lower_loop(&problem).expect("temp-chain CHC should map");
    assert_eq!(
        lowering.ts.num_state_vars, 2,
        "query temp-chain must resolve to args so the COI is {{acc, count[0]}}"
    );
    let model = try_prove_chc_loop(&problem, Duration::from_secs(15))
        .expect("lane should produce a candidate");
    let ok = crate::engines::validate_external_invariant_model(
        &problem,
        &model,
        &crate::PdrConfig::production(false),
    )
    .expect("validation should not error");
    assert!(
        ok,
        "resolved-temp candidate must re-validate on the original problem"
    );
}

#[test]
fn temp_chain_false_parity_not_safe() {
    // step=2: count[0] pinned while acc toggles -> acc != count[0] reachable. Even
    // with the temp resolution, the lane must NOT produce a validating candidate.
    let problem = bv_temp_chain_parity_problem(2);
    assert!(
        !validates(&problem),
        "false-parity temp-chain must not validate"
    );
}

// --- Gap C: lift const-folds the summarized-call accumulator update ----------

#[test]
fn constite_acc_update_lift_validates() {
    // acc' is the REAL summarized-call shape `Ite(true, Not(acc), acc)` (a const-
    // condition Select). Before the Gap-C const-fold `invert_head_arg` cannot invert
    // it, the lifted image drops the acc<=>count[0] correlation, and the candidate
    // FAILS re-validation. Folding `Ite(true, x, y) -> x` makes it invert to `!acc`,
    // so the lift produces a model the word-level validator accepts.
    let problem = bv64_real_ssa_cfg_constite(1);
    let model = try_prove_chc_loop(&problem, Duration::from_secs(30))
        .expect("lane should produce a candidate for the const-Ite CFG");
    assert_eq!(
        model.len(),
        problem.predicates().len(),
        "model covers all blocks"
    );
    let ok = crate::engines::validate_external_invariant_model(
        &problem,
        &model,
        &crate::PdrConfig::production(false),
    )
    .expect("validation should not error");
    assert!(ok, "const-folded acc-update candidate must re-validate");
}

#[test]
fn constite_false_parity_not_safe() {
    // step=2 with the const-Ite acc update: parity reachably false -> must NOT
    // produce a validating candidate.
    let problem = bv64_real_ssa_cfg_constite(2);
    assert!(
        !validates(&problem),
        "false-parity const-Ite CFG must not validate"
    );
}

// --- The REAL obl2 dump is fail-closed/degenerate: the lane must DECLINE -----

#[test]
fn real_obl2_thread_split_is_declined() {
    // EXACT reconstruction of obl2-dump.txt. It linearizes cleanly to one arity-2
    // predicate (9 latches), but every block carries an unsupported-instruction
    // `error :- bbN /\ true` fail-closed edge (model-checker-consumer `add_unsupported_error`),
    // so after linearization `bad` contains a constant-true disjunct and the mutable
    // acc/count cells (`load_result_6/7`) are free (not threaded into the predicate
    // signature). `bad` therefore fans in to NO state latch (coi 9->0). The Gap-B
    // soundness guard DECLINES (returns None) instead of fabricating a spurious init
    // `Unsafe` — the correct candidate-only behavior for a genuinely un-provable
    // (fail-closed) obligation.
    let problem = real_obl2_thread_split();
    assert_eq!(problem.predicates().len(), 7);
    assert_eq!(problem.clauses().len(), 16);
    let (lin, _hdr) = linearize_to_single_loop(&problem).expect("obl2 linearizes to one predicate");
    assert_eq!(
        lin.predicates().len(),
        1,
        "obl2 collapses to a single arity-2 header"
    );
    assert!(
        lower_loop(&problem).is_none(),
        "coi-empty guard must decline the fail-closed obligation"
    );
    assert!(
        try_prove_chc_loop(&problem, Duration::from_secs(10)).is_none(),
        "the lane must contribute no candidate for the fail-closed obl2"
    );
}

#[test]
fn diag_extract_vs_bvand_equiv() {
    // Minimal: Q(acc, count) with invariant acc <=> BvExtract(0,0)(count)==1,
    // query Q /\ Not(acc <=> (BvAnd(count,1)==1)) -> false. If validate REJECTS,
    // the validator cannot close BvExtract(0,0)==1 <=> BvAnd(count,1)==1.
    let w = |n| ChcSort::BitVec(n);
    let mut p = ChcProblem::new();
    let q = p.declare_predicate("Q", vec![ChcSort::Bool, w(64)]);
    let acc = ChcExpr::Var(ChcVar::new("acc", ChcSort::Bool));
    let count = ChcExpr::Var(ChcVar::new("count", w(64)));
    let ext0 = op(
        ChcOp::Eq,
        vec![
            op(ChcOp::BvExtract(0, 0), vec![count.clone()]),
            ChcExpr::BitVec(1, 1),
        ],
    );
    let bvand0 = op(
        ChcOp::Eq,
        vec![
            op(ChcOp::BvAnd, vec![count.clone(), ChcExpr::BitVec(1, 64)]),
            ChcExpr::BitVec(1, 64),
        ],
    );
    // fact Q(false,0); we only need the query check though.
    p.add_clause(HornClause::new(
        ClauseBody::empty(),
        ClauseHead::Predicate(q, vec![ChcExpr::Bool(false), ChcExpr::BitVec(0, 64)]),
    ));
    let bad = op(ChcOp::Not, vec![op(ChcOp::Eq, vec![acc.clone(), bvand0])]);
    p.add_clause(HornClause::new(
        ClauseBody::new(vec![(q, vec![acc.clone(), count.clone()])], Some(bad)),
        ClauseHead::False,
    ));
    let mut model = InvariantModel::new();
    let qv = vec![
        ChcVar::new("acc", ChcSort::Bool),
        ChcVar::new("count", w(64)),
    ];
    let inv = op(ChcOp::Eq, vec![acc.clone(), ext0]);
    model.set(q, PredicateInterpretation::new(qv, inv));
    let ok = crate::engines::validate_external_invariant_model(
        &p,
        &model,
        &crate::PdrConfig::production(false),
    )
    .unwrap();
    eprintln!("DIAG extract-vs-bvand validate => {ok}");
    assert!(
        ok,
        "validator should prove BvExtract(0,0)==1 <=> BvAnd(count,1)==1"
    );
}

// ---------------------------------------------------------------------------
// W2-i1: BRANCHING-BODY single loops via the disjunctive Init=⋁facts /
// T=⋁T_i encoding. A real nondeterministic-branch loop body linearizes to
// SEVERAL self-recursive transitions over one predicate; the lane used to
// reject anything but exactly one transition. The disjunctive transition
// relation admits them (completeness gain) while remaining an
// over-approximation (no false proof).
// ---------------------------------------------------------------------------

/// A branching-body single loop over `P(x: Int)`:
///   fact:  P(0)
///   T1:    P(x) -> P(x + `a`)     [nondeterministic branch 1]
///   T2:    P(x) -> P(x + `b`)     [nondeterministic branch 2]
///   query: P(x) /\ (x mod 2 == 1) -> false   (bad iff x is odd)
/// Two transitions over the SAME predicate, each with a different update and no
/// guard — the model checker must nondeterministically pick a branch per step.
fn branching_evenness_problem(a: i64, b: i64) -> ChcProblem {
    let mut p = ChcProblem::new();
    let pid = p.declare_predicate("P", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    let x_e = ChcExpr::Var(x);

    // fact: P(0)
    p.add_clause(HornClause::new(
        ClauseBody::empty(),
        ClauseHead::Predicate(pid, vec![ChcExpr::Int(0)]),
    ));
    // T1: P(x) -> P(x + a)
    p.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(pid, vec![x_e.clone()])]),
        ClauseHead::Predicate(
            pid,
            vec![op(
                ChcOp::Add,
                vec![x_e.clone(), ChcExpr::Int(i128::from(a))],
            )],
        ),
    ));
    // T2: P(x) -> P(x + b)
    p.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(pid, vec![x_e.clone()])]),
        ClauseHead::Predicate(
            pid,
            vec![op(
                ChcOp::Add,
                vec![x_e.clone(), ChcExpr::Int(i128::from(b))],
            )],
        ),
    ));
    // query: P(x) /\ (x mod 2 == 1) -> false
    let odd = op(
        ChcOp::Eq,
        vec![
            op(ChcOp::Mod, vec![x_e.clone(), ChcExpr::Int(2)]),
            ChcExpr::Int(1),
        ],
    );
    p.add_clause(HornClause::new(
        ClauseBody::new(vec![(pid, vec![x_e])], Some(odd)),
        ClauseHead::False,
    ));
    p
}

#[test]
fn branching_body_safe_loop_maps_and_proves() {
    // +2 / +4 both preserve evenness from x=0, so `x mod 2 == 1` is unreachable.
    // Two transitions over one predicate: REJECTED by the old ==1 gate, ADMITTED
    // now. This is the W2-i1 completeness gain.
    let problem = branching_evenness_problem(2, 4);

    // Sanity: the CHC really has two self-recursive transitions.
    let pid = problem.predicates()[0].id;
    let n_trans = problem
        .clauses()
        .iter()
        .filter(|c| {
            matches!(&c.head, ClauseHead::Predicate(h, _) if *h == pid)
                && !c.body.predicates.is_empty()
        })
        .count();
    assert_eq!(n_trans, 2, "two-branch body -> two transitions");

    // (Edit 3) the relaxed gate lets the multi-transition CHC MAP.
    assert!(
        lower_loop(&problem).is_some(),
        "branching-body single loop must now map (relaxed ==1 gate)"
    );

    // The full lane converges to Safe and returns a candidate invariant (x[0]==0).
    let model = try_prove_chc_loop(&problem, Duration::from_secs(10));
    assert!(
        model.is_some(),
        "safe branching loop must yield a candidate invariant (completeness gain)"
    );

    // The candidate must survive the trusted word-level re-validation.
    let ok = crate::engines::validate_external_invariant_model(
        &problem,
        &model.unwrap(),
        &crate::PdrConfig::production(false),
    )
    .expect("validation should not error");
    assert!(
        ok,
        "safe branching-loop candidate must re-validate word-level"
    );
}

#[test]
fn branching_body_unsafe_loop_no_false_proof() {
    // +2 keeps evenness but +1 makes x odd, so `x mod 2 == 1` IS reachable
    // (choose T2 once from x=0). The disjunctive encoding is an over-approximation,
    // so it must NOT forge a proof: either the lane declines (None) or any candidate
    // it returns fails the trusted word-level re-validation.
    let problem = branching_evenness_problem(2, 1);

    match try_prove_chc_loop(&problem, Duration::from_secs(10)) {
        None => {
            // Lane declined / did not converge to Safe — no false proof. Good.
        }
        Some(model) => {
            let ok = crate::engines::validate_external_invariant_model(
                &problem,
                &model,
                &crate::PdrConfig::production(false),
            );
            assert!(
                !matches!(ok, Ok(true)),
                "unsafe branching loop must NOT produce a surviving proof; got {ok:?}"
            );
        }
    }
}

#[test]
fn single_transition_still_maps_and_proves() {
    // Reduction equivalence: the classic 1-fact/1-transition count-parity loop must
    // still map and prove Safe through the disjunctive path (chain collapses to the
    // prior stuttering single-update).
    let problem = count_parity_problem(1);
    let lowering = lower_loop(&problem).expect("1-transition count-parity must still map");
    // COI slice still keeps exactly {acc, count[0]} — unchanged by the new encoding.
    assert_eq!(lowering.ts.num_state_vars, 2);
    let mut solver = Ic3Solver::new(lowering.ts, false);
    assert!(
        matches!(solver.solve(), Ic3Result::Safe { .. }),
        "1-transition parity loop must still be proven Safe (reduction equivalence)"
    );
    assert!(
        try_prove_chc_loop(&problem, Duration::from_secs(5)).is_some(),
        "1-transition lane must still return a candidate (reduction equivalence)"
    );
}
