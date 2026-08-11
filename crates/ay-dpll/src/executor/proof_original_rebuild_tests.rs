// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unit tests for the substitution bridge's `trans`-through-a-definition leg
//! (`proof_original_rebuild.rs`).
//!
//! These exercise the PLANNER directly, which is where the authority argument
//! lives: the planner may only build a derivation out of assertions the
//! problem authored, so a definition the problem does not contain must make
//! planning fail rather than produce a step. The end-to-end shape (a real
//! store-flat UNSAT self-certifying) is covered in `executor/proof/tests.rs`.

use super::*;

struct SeqPushBackRowFixture {
    zero_seed: TermId,
    seed_len: TermId,
    goal: TermId,
    array: TermId,
    read_index: TermId,
    len: TermId,
    value: TermId,
}

fn seq_push_back_row_fixture(exec: &mut Executor) -> SeqPushBackRowFixture {
    let terms = &mut exec.ctx.terms;
    let array_sort = Sort::array(Sort::Int, Sort::Int);
    let array = terms.mk_var("seq_array", array_sort.clone());
    let read_index = terms.mk_var("seq_offset", Sort::Int);
    let seed_len = terms.mk_var("seq_len_before", Sort::Int);
    let len = terms.mk_var("seq_len_proxy", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0_u8));
    let value = terms.mk_int(BigInt::from(30_u8));
    let store_index = terms.mk_app(Symbol::named("+"), [read_index, len], Sort::Int);
    let stored = terms.mk_app(
        Symbol::named("store"),
        [array, store_index, value],
        array_sort,
    );
    let selected = terms.mk_app(Symbol::named("select"), [stored, read_index], Sort::Int);
    let row_eq = terms.mk_app(Symbol::named("="), [value, selected], Sort::Bool);
    let goal = terms.mk_not_raw(row_eq);
    let zero_seed = terms.mk_app(Symbol::named("="), [zero, seed_len], Sort::Bool);
    let seed_len = terms.mk_app(Symbol::named("="), [seed_len, len], Sort::Bool);
    SeqPushBackRowFixture {
        zero_seed,
        seed_len,
        goal,
        array,
        read_index,
        len,
        value,
    }
}

fn terminal_empty_trust_proof() -> Proof {
    let mut proof = Proof::new();
    proof.add_rule_step(AletheRule::Trust, Vec::new(), Vec::new(), Vec::new());
    proof
}

#[test]
fn authenticated_seq_push_back_row_rebuilds_with_two_exact_lia_equalities() {
    let mut exec = Executor::new();
    let f = seq_push_back_row_fixture(&mut exec);
    let authored = vec![f.zero_seed, f.seed_len, f.goal];
    let mut proof = terminal_empty_trust_proof();

    exec.plan_authenticated_seq_push_back_row1(&authored)
        .expect("the exact two-equality fixture must produce a proof plan");
    assert!(exec.try_rebuild_authenticated_seq_push_back_row1(&mut proof, &authored));
    let quality = ay_proof::check_proof_strict(&proof, &exec.ctx.terms)
        .expect("the rebuilt LIA + guarded ROW1 proof must strictly replay");
    assert!(quality.is_complete());
    assert!(
        ay_proof::validate_reachable_assumes_in_problem_scope(&proof, &authored).is_ok(),
        "every reachable assumption must be one of the exact authored roots"
    );
    assert!(proof.steps.iter().all(|step| !matches!(
        step,
        ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::Generic,
            ..
        }
    )));
    let assumed: Vec<TermId> = proof
        .steps
        .iter()
        .filter_map(|step| match step {
            ProofStep::Assume(term) => Some(*term),
            _ => None,
        })
        .collect();
    assert_eq!(
        assumed, authored,
        "both LIA links and the goal are consumed"
    );
}

#[test]
fn authenticated_seq_push_back_row_refuses_missing_or_changed_lia_link() {
    let mut exec = Executor::new();
    let f = seq_push_back_row_fixture(&mut exec);

    for authored in [vec![f.zero_seed, f.goal], {
        let other_len = exec.ctx.terms.mk_var("other_len", Sort::Int);
        let TermData::App(Symbol::Named(_), args) = exec.ctx.terms.get(f.seed_len).clone() else {
            panic!("fixture link must be an equality")
        };
        let changed = exec
            .ctx
            .terms
            .mk_app(Symbol::named("="), [args[0], other_len], Sort::Bool);
        vec![f.zero_seed, changed, f.goal]
    }] {
        let mut proof = terminal_empty_trust_proof();
        assert!(
            !exec.try_rebuild_authenticated_seq_push_back_row1(&mut proof, &authored),
            "a missing/changed authored length link must fail closed"
        );
        assert_eq!(
            ay_proof::terminal_trust_report(&proof).trust_rule_on_path,
            1
        );
    }
}

#[test]
fn authenticated_seq_push_back_row_refuses_changed_store_index_or_value() {
    let mut exec = Executor::new();
    let f = seq_push_back_row_fixture(&mut exec);
    let array_sort = Sort::array(Sort::Int, Sort::Int);

    let wrong_offset = exec.ctx.terms.mk_var("wrong_offset", Sort::Int);
    let wrong_store_index =
        exec.ctx
            .terms
            .mk_app(Symbol::named("+"), [wrong_offset, f.len], Sort::Int);
    let wrong_index_store = exec.ctx.terms.mk_app(
        Symbol::named("store"),
        [f.array, wrong_store_index, f.value],
        array_sort.clone(),
    );
    let wrong_index_select = exec.ctx.terms.mk_app(
        Symbol::named("select"),
        [wrong_index_store, f.read_index],
        Sort::Int,
    );
    let wrong_index_eq = exec.ctx.terms.mk_app(
        Symbol::named("="),
        [f.value, wrong_index_select],
        Sort::Bool,
    );
    let wrong_index_goal = exec.ctx.terms.mk_not_raw(wrong_index_eq);

    let store_index = exec
        .ctx
        .terms
        .mk_app(Symbol::named("+"), [f.read_index, f.len], Sort::Int);
    let stored = exec.ctx.terms.mk_app(
        Symbol::named("store"),
        [f.array, store_index, f.value],
        array_sort,
    );
    let selected =
        exec.ctx
            .terms
            .mk_app(Symbol::named("select"), [stored, f.read_index], Sort::Int);
    let wrong_value = exec.ctx.terms.mk_int(BigInt::from(31_u8));
    let wrong_value_eq =
        exec.ctx
            .terms
            .mk_app(Symbol::named("="), [wrong_value, selected], Sort::Bool);
    let wrong_value_goal = exec.ctx.terms.mk_not_raw(wrong_value_eq);

    for goal in [wrong_index_goal, wrong_value_goal] {
        let authored = vec![f.zero_seed, f.seed_len, goal];
        let mut proof = terminal_empty_trust_proof();
        assert!(
            !exec.try_rebuild_authenticated_seq_push_back_row1(&mut proof, &authored),
            "a changed store index/value must not match the exact ROW1 lane"
        );
        assert_eq!(
            ay_proof::terminal_trust_report(&proof).trust_rule_on_path,
            1
        );
    }
}

/// Build the store-flat fixture:
///
/// ```text
///   b1 = (store a1 i1 e1)      b2 = (store b1 i2 e2)
/// ```
///
/// and return `(b2, expanded)` where `expanded` is the fully substituted
/// `(store (store a1 i1 e1) i2 e2)` — exactly what
/// `substitute_store_flat_equalities` leaves in the assertion the proof
/// assumes — plus the two authored defining equalities.
struct StoreChain {
    b2: TermId,
    expanded: TermId,
    def_b1: TermId,
    def_b2: TermId,
}

fn store_chain(exec: &mut Executor) -> StoreChain {
    let index = Sort::Uninterpreted("Index".to_string());
    let element = Sort::Uninterpreted("Element".to_string());
    let array = Sort::array(index.clone(), element.clone());
    let terms = &mut exec.ctx.terms;

    let a1 = terms.mk_var("a1", array.clone());
    let b1 = terms.mk_var("b1", array.clone());
    let b2 = terms.mk_var("b2", array.clone());
    let i1 = terms.mk_var("i1", index.clone());
    let i2 = terms.mk_var("i2", index);
    let e1 = terms.mk_var("e1", element.clone());
    let e2 = terms.mk_var("e2", element);

    let store_a1 = terms.mk_app(Symbol::named("store"), [a1, i1, e1], array.clone());
    let store_b1 = terms.mk_app(Symbol::named("store"), [b1, i2, e2], array.clone());
    let expanded = terms.mk_app(Symbol::named("store"), [store_a1, i2, e2], array);

    let def_b1 = terms.mk_app(Symbol::named("="), [b1, store_a1], Sort::Bool);
    let def_b2 = terms.mk_app(Symbol::named("="), [b2, store_b1], Sort::Bool);

    StoreChain {
        b2,
        expanded,
        def_b1,
        def_b2,
    }
}

/// POSITIVE: with BOTH authored defining equalities present, the planner walks
/// the chain — `trans` through `b2`'s definition, then congruence on the
/// store's array argument, then `trans` through `b1`'s definition — and every
/// premise it needs is one of the authored assertions.
#[test]
fn plan_eq_bridges_a_store_chain_through_authored_definitions() {
    let mut exec = Executor::new();
    let chain = store_chain(&mut exec);
    let originals = vec![chain.def_b1, chain.def_b2];

    let mut budget = EQ_PLAN_BUDGET;
    let plan = exec
        .plan_eq(chain.b2, chain.expanded, &originals, 0, &mut budget)
        .expect("the store chain must be derivable from its authored definitions");

    assert!(
        matches!(plan.kind, EqPlanKind::Trans { .. }),
        "the top of the chain must be a `trans` through b2's definition"
    );

    // Every premise the plan needs is an AUTHORED assertion — the whole point
    // of the #8821 gate.
    let mut assumed = Vec::new();
    plan.collect_assumed(&mut assumed);
    assert!(
        !assumed.is_empty(),
        "a chain bridge must rest on real premises, not on nothing"
    );
    for term in &assumed {
        assert!(
            originals.contains(term),
            "planner assumed a non-authored term {term:?}"
        );
    }
    assert!(
        assumed.contains(&chain.def_b1) && assumed.contains(&chain.def_b2),
        "both links of the chain must be used"
    );
}

/// NEGATIVE (the load-bearing one): drop `b1`'s defining equality from the
/// authored set. The chain is now unreachable, and the planner must FAIL
/// rather than invent the missing link — a fabricated `(= b1 (store a1 i1 e1))`
/// would be a free axiom laundered into an `assume`.
#[test]
fn plan_eq_refuses_to_fabricate_an_absent_defining_equality() {
    let mut exec = Executor::new();
    let chain = store_chain(&mut exec);
    // `b2`'s definition is authored; `b1`'s is NOT.
    let originals = vec![chain.def_b2];

    let mut budget = EQ_PLAN_BUDGET;
    let plan = exec.plan_eq(chain.b2, chain.expanded, &originals, 0, &mut budget);
    assert!(
        plan.is_none(),
        "with b1's defining equality absent the bridge must fail closed, \
         not manufacture the missing link"
    );
}

#[test]
fn plan_eq_bridges_pinned_concat_to_folded_literal() {
    let mut exec = Executor::new();
    let terms = &mut exec.ctx.terms;
    let op = terms.mk_var("op", Sort::bitvec(8));
    let lhs = terms.mk_var("lhs", Sort::bitvec(8));
    let rhs = terms.mk_var("rhs", Sort::bitvec(8));
    let one = terms.mk_bitvec(BigInt::from(1_u8), 8);
    let sixty_three = terms.mk_bitvec(BigInt::from(63_u8), 8);
    let sixty_four = terms.mk_bitvec(BigInt::from(64_u8), 8);
    let inner = terms.mk_app(Symbol::named("concat"), [lhs, rhs], Sort::bitvec(16));
    let symbolic = terms.mk_app(Symbol::named("concat"), [op, inner], Sort::bitvec(24));
    let folded = terms.mk_bitvec(BigInt::from(0x013f40_u32), 24);
    let pin_op = terms.mk_app(Symbol::named("="), [op, one], Sort::Bool);
    let pin_lhs = terms.mk_app(Symbol::named("="), [lhs, sixty_three], Sort::Bool);
    let pin_rhs = terms.mk_app(Symbol::named("="), [rhs, sixty_four], Sort::Bool);
    let originals = vec![pin_op, pin_lhs, pin_rhs];

    let mut budget = EQ_PLAN_BUDGET;
    let plan = exec
        .plan_eq(symbolic, folded, &originals, 0, &mut budget)
        .expect("authored component pins must certify the folded concat");
    assert!(
        plan.uses_ground_evaluate(),
        "folded concat bridge must use the externally checkable evaluate rule"
    );
    let mut assumed = Vec::new();
    plan.collect_assumed(&mut assumed);
    assert_eq!(assumed.len(), originals.len());
    assert!(originals.iter().all(|term| assumed.contains(term)));

    let mut proof = Proof::new();
    let assume_ids: HashMap<TermId, ProofId> = originals
        .iter()
        .map(|&term| (term, proof.add_assume(term, None)))
        .collect();
    let negated_goal = exec.ctx.terms.mk_not_raw(plan.eq);
    let negated_goal_assume = proof.add_assume(negated_goal, None);
    let goal_unit = Executor::emit_eq_plan(&mut proof, &plan, &assume_ids)
        .expect("planned concat bridge must emit");
    proof.add_resolution(Vec::new(), plan.eq, goal_unit, negated_goal_assume);
    ay_proof::check_proof_strict(&proof, &exec.ctx.terms)
        .expect("every emitted concat bridge step must pass the strict checker");
}

#[test]
fn plan_eq_uses_direct_evaluate_for_an_already_ground_concat() {
    let mut exec = Executor::new();
    let terms = &mut exec.ctx.terms;
    let op = terms.mk_bitvec(BigInt::from(1_u8), 8);
    let lhs = terms.mk_bitvec(BigInt::from(63_u8), 8);
    let rhs = terms.mk_bitvec(BigInt::from(64_u8), 8);
    let inner = terms.mk_app(Symbol::named("concat"), [lhs, rhs], Sort::bitvec(16));
    let ground = terms.mk_app(Symbol::named("concat"), [op, inner], Sort::bitvec(24));
    let folded = terms.mk_bitvec(BigInt::from(0x013f40_u32), 24);

    let mut budget = EQ_PLAN_BUDGET;
    let plan = exec
        .plan_eq(ground, folded, &[], 0, &mut budget)
        .expect("the exact ground concat evaluation needs no authored equality");
    assert!(
        matches!(plan.kind, EqPlanKind::BvGroundEvaluate),
        "a ground concat must not be wrapped in a redundant transitivity step"
    );
    let mut assumed = Vec::new();
    plan.collect_assumed(&mut assumed);
    assert!(
        assumed.is_empty(),
        "closed evaluation must not invent an authored premise"
    );

    let mut proof = Proof::new();
    let negated_goal = exec.ctx.terms.mk_not_raw(plan.eq);
    let negated_goal_assume = proof.add_assume(negated_goal, None);
    let goal_unit = Executor::emit_eq_plan(&mut proof, &plan, &HashMap::default())
        .expect("direct ground evaluation must emit");
    proof.add_resolution(Vec::new(), plan.eq, goal_unit, negated_goal_assume);
    ay_proof::check_proof_strict(&proof, &exec.ctx.terms)
        .expect("direct evaluate plus resolution must pass the strict checker");
}

#[test]
fn plan_eq_refuses_folded_concat_without_all_pins() {
    let mut exec = Executor::new();
    let terms = &mut exec.ctx.terms;
    let op = terms.mk_var("op", Sort::bitvec(8));
    let lhs = terms.mk_var("lhs", Sort::bitvec(8));
    let rhs = terms.mk_var("rhs", Sort::bitvec(8));
    let one = terms.mk_bitvec(BigInt::from(1_u8), 8);
    let sixty_three = terms.mk_bitvec(BigInt::from(63_u8), 8);
    let inner = terms.mk_app(Symbol::named("concat"), [lhs, rhs], Sort::bitvec(16));
    let symbolic = terms.mk_app(Symbol::named("concat"), [op, inner], Sort::bitvec(24));
    let folded = terms.mk_bitvec(BigInt::from(0x013f40_u32), 24);
    let pin_op = terms.mk_app(Symbol::named("="), [op, one], Sort::Bool);
    let pin_lhs = terms.mk_app(Symbol::named("="), [lhs, sixty_three], Sort::Bool);
    // `rhs = #x40` is deliberately absent: no closed BV lemma may replace an
    // authored premise that the problem did not provide.
    let originals = vec![pin_op, pin_lhs];

    let mut budget = EQ_PLAN_BUDGET;
    assert!(
        exec.plan_eq(symbolic, folded, &originals, 0, &mut budget)
            .is_none(),
        "the folded concat bridge must fail closed when one pin is missing"
    );
}

#[test]
fn plan_eq_refuses_folded_concat_above_64_bits() {
    let mut exec = Executor::new();
    let terms = &mut exec.ctx.terms;
    let high = terms.mk_var("high", Sort::bitvec(1));
    let low = terms.mk_var("low", Sort::bitvec(64));
    let high_value = terms.mk_bitvec(BigInt::from(1_u8), 1);
    let low_value = terms.mk_bitvec(BigInt::from(0_u8), 64);
    let symbolic = terms.mk_app(Symbol::named("concat"), [high, low], Sort::bitvec(65));
    let folded = terms.mk_bitvec(BigInt::from(1_u8) << 64_u32, 65);
    let pin_high = terms.mk_app(Symbol::named("="), [high, high_value], Sort::Bool);
    let pin_low = terms.mk_app(Symbol::named("="), [low, low_value], Sort::Bool);

    let mut budget = EQ_PLAN_BUDGET;
    assert!(
        exec.plan_eq(symbolic, folded, &[pin_high, pin_low], 0, &mut budget)
            .is_none(),
        "concat planning must fail before splitting a BV literal above the exact u64 envelope"
    );
}

/// NEGATIVE: nothing at all is authored. Even the first link must not appear.
#[test]
fn plan_eq_refuses_a_chain_with_no_authored_definitions() {
    let mut exec = Executor::new();
    let chain = store_chain(&mut exec);

    let mut budget = EQ_PLAN_BUDGET;
    assert!(
        exec.plan_eq(chain.b2, chain.expanded, &[], 0, &mut budget)
            .is_none(),
        "an empty authored set can derive nothing"
    );
}

/// NEGATIVE: a leaf bridged from the WRONG authored assertion must be
/// rejected. Here the problem authors a decoy predicate over a DIFFERENT
/// variable (`c2`), whose arguments cannot be connected to the substituted
/// leaf's. `plan_substitution_bridge` must not latch onto the decoy just
/// because it shares the goal's head symbol and arity.
#[test]
fn plan_substitution_bridge_rejects_an_unconnected_authored_source() {
    let mut exec = Executor::new();
    let chain = store_chain(&mut exec);
    let index = Sort::Uninterpreted("Index".to_string());
    let element = Sort::Uninterpreted("Element".to_string());
    let array = Sort::array(index, element);

    // Decoy: `(not (= c2 d2))`, same head (`=`) and arity as the goal, but
    // over variables with no authored definitions at all.
    let (decoy, goal) = {
        let terms = &mut exec.ctx.terms;
        let c2 = terms.mk_var("c2", array.clone());
        let d2 = terms.mk_var("d2", array.clone());
        let other = terms.mk_var("other", array);
        let decoy_eq = terms.mk_app(Symbol::named("="), [c2, d2], Sort::Bool);
        let decoy = terms.mk_not_raw(decoy_eq);
        // The substituted leaf: `(not (= expanded other))`.
        let goal_eq = terms.mk_app(Symbol::named("="), [chain.expanded, other], Sort::Bool);
        let goal = terms.mk_not_raw(goal_eq);
        (decoy, goal)
    };

    // The decoy and both real definitions are authored; the leaf still cannot
    // be derived, because no authored equality connects `other`.
    let originals = vec![chain.def_b1, chain.def_b2, decoy];
    assert!(
        exec.plan_substitution_bridge(goal, &originals).is_none(),
        "the bridge must not source a leaf from an authored assertion whose \
         arguments it cannot actually connect"
    );
}

/// The planner's search is bounded: a budget of zero derives nothing, so a
/// pathological original set can never spin the export.
#[test]
fn plan_eq_respects_its_work_budget() {
    let mut exec = Executor::new();
    let chain = store_chain(&mut exec);
    let originals = vec![chain.def_b1, chain.def_b2];

    let mut budget = 0;
    assert!(
        exec.plan_eq(chain.b2, chain.expanded, &originals, 0, &mut budget)
            .is_none(),
        "an exhausted budget must fail closed"
    );

    // And the same query succeeds once the budget is restored, proving the
    // failure above was the budget and not the fixture.
    let mut budget = EQ_PLAN_BUDGET;
    assert!(exec
        .plan_eq(chain.b2, chain.expanded, &originals, 0, &mut budget)
        .is_some());
}

/// The bridge budget is total for the GOAL, not reset for every same-head
/// authored candidate. With one node, the bad first candidate consumes the
/// allowance and the later derivable candidate must not receive a fresh one.
#[test]
fn substitution_bridge_budget_spans_all_source_candidates() {
    let mut exec = Executor::new();
    let sort = Sort::Uninterpreted("T".to_string());
    let (bad_source, good_source, definition, goal) = {
        let terms = &mut exec.ctx.terms;
        let x = terms.mk_var("x", sort.clone());
        let a = terms.mk_var("a", sort.clone());
        let b = terms.mk_var("b", sort);
        let bad_source = terms.mk_app(Symbol::named("P"), [x], Sort::Bool);
        let good_source = terms.mk_app(Symbol::named("P"), [a], Sort::Bool);
        let definition = terms.mk_app(Symbol::named("="), [a, b], Sort::Bool);
        let goal = terms.mk_app(Symbol::named("P"), [b], Sort::Bool);
        (bad_source, good_source, definition, goal)
    };
    let originals = vec![bad_source, good_source, definition];

    let mut one_node = 1;
    assert!(
        exec.plan_substitution_bridge_with_budget(goal, &originals, &mut one_node)
            .is_none(),
        "a failed source candidate must not reset the goal's work budget"
    );
    assert_eq!(one_node, 0);

    let mut two_nodes = 2;
    assert!(
        exec.plan_substitution_bridge_with_budget(goal, &originals, &mut two_nodes)
            .is_some(),
        "the later authored source is derivable when the total budget permits it"
    );
    assert_eq!(two_nodes, 0);
}

/// `reachable_step_mask` must agree with the #8821 gate's own cone walk: the
/// dead branch is excluded, the live one is not. This is what lets the bridge
/// stop vetoing a whole proof over a leaf that carries no authority claim.
#[test]
fn reachable_step_mask_matches_the_authority_gate_cone() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let not_p = terms.mk_not_raw(p);
    let dead = terms.mk_var("dead", Sort::Bool);

    let mut proof = Proof::new();
    let live_a = proof.add_assume(p, None); // 0: reachable
    let live_b = proof.add_assume(not_p, None); // 1: reachable
    let _dead_assume = proof.add_assume(dead, None); // 2: NOT reachable
    proof.add_resolution(Vec::new(), p, live_a, live_b); // 3: the empty clause

    let mask = Executor::reachable_step_mask(&proof);
    assert_eq!(mask, vec![true, true, false, true]);

    // The authority gate agrees: with only `p` and `(not p)` in problem scope,
    // the dead `dead` assume does NOT make the proof unauthorized.
    assert!(
        ay_proof::validate_reachable_assumes_in_problem_scope(&proof, &[p, not_p]).is_ok(),
        "a dead assume is outside the cone the #8821 gate inspects"
    );
}
