// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The instance-seeded equality closure accepts exactly the refutations its
//! strict gate re-derives, and declines (leaving the rejected proof as it was)
//! whenever a guard, an endpoint, or a premise is not independently justified.

use super::*;
use ay_frontend::parse;

/// Declare and assert `script` (no `check-sat`), so the authored scope is the
/// elaborated assertion stack exactly as the cascade sees it.
fn authored(script: &str) -> Executor {
    let mut exec = Executor::new();
    let commands = parse(script).expect("fixture parses");
    exec.execute_all(&commands).expect("fixture elaborates");
    exec
}

/// The whole-problem closer the engine leaves when it records no derivation.
fn bare_trust_closure() -> Proof {
    let mut proof = Proof::new();
    proof.add_rule_step(AletheRule::Trust, Vec::new(), Vec::new(), Vec::new());
    proof
}

fn rule_count(proof: &Proof, wanted: &AletheRule) -> usize {
    proof
        .steps
        .iter()
        .filter(|step| matches!(step, ProofStep::Step { rule, .. } if rule == wanted))
        .count()
}

/// The printed `:args` of every `forall_inst` step.
fn forall_inst_args(exec: &Executor, proof: &Proof) -> Vec<Vec<String>> {
    proof
        .steps
        .iter()
        .filter_map(|step| match step {
            ProofStep::Step {
                rule: AletheRule::ForallInst,
                args,
                ..
            } => Some(
                args.iter()
                    .map(|&arg| ay_proof::format_term_alethe(&exec.ctx.terms, arg))
                    .collect(),
            ),
            _ => None,
        })
        .collect()
}

/// Run the new member and require a complete, trust-free, authored-scope
/// refutation; returns it.
fn closes(exec: &mut Executor) -> Proof {
    let mut proof = bare_trust_closure();
    exec.replace_with_authored_instance_closure_refutation(&mut proof);
    let quality = exec
        .check_proof_strict_with_datatypes(&proof)
        .expect("the rebuilt refutation must pass the plain strict checker");
    assert!(quality.is_complete());
    assert!(ay_proof::terminal_trust_report(&proof).is_trust_free());
    let scope = exec.exact_concrete_authored_scope();
    ay_proof::validate_reachable_assumes_in_problem_scope(&proof, &scope)
        .expect("every reachable assume is an exact authored root");
    assert!(Executor::proof_derives_empty_clause(&proof));
    proof
}

/// Run the new member and require that it left the rejected proof untouched.
fn declines(exec: &mut Executor) {
    let mut proof = bare_trust_closure();
    exec.replace_with_authored_instance_closure_refutation(&mut proof);
    assert_eq!(proof.steps.len(), 1, "the rejected closer must be kept");
    assert!(exec.check_proof_strict_with_datatypes(&proof).is_err());
}

/// `uf_scalar` in miniature: the matched instance's guard `(bvult k 9)` is an
/// authored root and the chain ends at the authored `distinct`.
const SYMBOLIC_GUARD: &str = r#"
(set-logic ALL)
(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(declare-const x (_ BitVec 8))
(declare-const fill (_ BitVec 8))
(declare-const k (_ BitVec 8))
(declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
(assert (= fill (f x)))
(assert (bvult k (_ bv9 8)))
(assert (forall ((i (_ BitVec 8))) (=> (bvult i (_ bv9 8)) (= (select a i) (f x)))))
(assert (distinct (select a k) fill))
"#;

/// `uf_false_matrix` in miniature: the guard `(bvult 4 5)` is closed, so it is
/// discharged by `evaluate`, and the chain ends at two distinct constants.
const CLOSED_GUARD: &str = r#"
(set-logic ALL)
(declare-fun g (Bool (_ BitVec 8)) (_ BitVec 1))
(assert (forall ((i (_ BitVec 8))) (=> (bvult i (_ bv5 8)) (= (g false i) (_ bv1 1)))))
(assert (= (g false (_ bv4 8)) (_ bv0 1)))
"#;

/// `uf_false_query` in miniature: no quantifier, three authored equalities.
const CONSTANT_CHAIN: &str = r#"
(set-logic ALL)
(declare-const v0 (_ BitVec 1))
(declare-const v1 (_ BitVec 1))
(assert (= v0 (_ bv1 1)))
(assert (= v1 v0))
(assert (= v1 (_ bv0 1)))
"#;

#[test]
fn authored_guard_instance_closes_on_the_authored_disequality() {
    let mut exec = authored(SYMBOLIC_GUARD);
    let proof = closes(&mut exec);
    assert_eq!(forall_inst_args(&exec, &proof), vec![vec!["k".to_string()]]);
    assert_eq!(rule_count(&proof, &AletheRule::Evaluate), 0);
}

#[test]
fn closed_guard_is_evaluated_and_distinct_constants_close() {
    let mut exec = authored(CLOSED_GUARD);
    let proof = closes(&mut exec);
    assert_eq!(
        forall_inst_args(&exec, &proof),
        vec![vec!["#b00000100".to_string()]]
    );
    // One `evaluate` for the guard, one for `(= #b1 #b0)`.
    assert_eq!(rule_count(&proof, &AletheRule::Evaluate), 2);
}

#[test]
fn ground_equality_chain_closes_on_distinct_constants() {
    let mut exec = authored(CONSTANT_CHAIN);
    let proof = closes(&mut exec);
    assert!(forall_inst_args(&exec, &proof).is_empty());
    assert_eq!(rule_count(&proof, &AletheRule::Evaluate), 1);
    assert!(rule_count(&proof, &AletheRule::EqTransitive) >= 2);
}

#[test]
fn the_plain_closure_member_still_declines_these_shapes() {
    // Counterfactual pin: the earlier cascade member is unchanged, so what
    // closes above is the new member and nothing it publishes moved.
    for script in [SYMBOLIC_GUARD, CLOSED_GUARD, CONSTANT_CHAIN] {
        let mut exec = authored(script);
        let mut proof = bare_trust_closure();
        exec.replace_with_exact_authored_equality_closure_refutation(&mut proof);
        assert_eq!(proof.steps.len(), 1, "{script}");
    }
}

#[test]
fn undischarged_symbolic_guard_declines() {
    // `(bvult k n)` is neither authored nor closed: the instance at `k` would
    // rest on an unproved guard, so no instance is seeded. (The problem is
    // satisfiable: `k` may lie outside the guarded range.)
    let mut exec = authored(
        r#"
(set-logic ALL)
(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(declare-const x (_ BitVec 8))
(declare-const fill (_ BitVec 8))
(declare-const k (_ BitVec 8))
(declare-const n (_ BitVec 8))
(declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
(assert (= fill (f x)))
(assert (forall ((i (_ BitVec 8))) (=> (bvult i n) (= (select a i) (f x)))))
(assert (distinct (select a k) fill))
"#,
    );
    declines(&mut exec);
}

#[test]
fn closed_guard_that_evaluates_false_declines() {
    // `(bvult 5 5)` is false: the instance at 5 is vacuous and the problem is
    // satisfiable.
    let mut exec = authored(
        r#"
(set-logic ALL)
(declare-fun g (Bool (_ BitVec 8)) (_ BitVec 1))
(assert (forall ((i (_ BitVec 8))) (=> (bvult i (_ bv5 8)) (= (g false i) (_ bv1 1)))))
(assert (= (g false (_ bv5 8)) (_ bv0 1)))
"#,
    );
    declines(&mut exec);
}

#[test]
fn equal_constant_endpoints_decline() {
    // The chain ends at `#b1` twice: nothing to refute (satisfiable).
    let mut exec = authored(
        r#"
(set-logic ALL)
(declare-const v0 (_ BitVec 1))
(declare-const v1 (_ BitVec 1))
(assert (= v0 (_ bv1 1)))
(assert (= v1 v0))
(assert (= v1 (_ bv1 1)))
"#,
    );
    declines(&mut exec);
}

#[test]
fn closed_guard_over_a_nested_operator_is_not_evaluated() {
    // Unsat at `i = #xff`, and AY's own evaluator admits the closed guard
    // `(= (bvsub #xff #x01) #xfe)`. Pinned carcara does not: inside `bvsub`
    // it reads `#xff` as the magnitude 1 and computes `0`, so it would refute
    // that `evaluate` step. Closed guards are therefore refuted only over
    // literal operands, and this instance is not seeded.
    let mut exec = authored(
        r#"
(set-logic ALL)
(declare-fun g ((_ BitVec 8)) (_ BitVec 8))
(assert (forall ((i (_ BitVec 8))) (=> (= (bvsub i #x01) #xfe) (= (g i) #x01))))
(assert (= (g #xff) #x00))
"#,
    );
    let terms = &mut exec.ctx.terms;
    let byte = |terms: &mut TermStore, value: u32| terms.mk_bitvec(value.into(), 8);
    let (all_ones, one, expected) = (byte(terms, 0xff), byte(terms, 1), byte(terms, 0xfe));
    let sort = terms.sort(one).clone();
    let difference = terms.mk_app(Symbol::named("bvsub"), [all_ones, one], sort);
    let guard = terms.mk_app(Symbol::named("="), [difference, expected], Sort::Bool);
    assert!(
        ay_proof::recognize_ground_evaluate(terms, guard),
        "counterfactual: the internal evaluator admits the nested guard"
    );
    assert!(!closed_comparison_over_literals(terms, guard));
    declines(&mut exec);
}

#[test]
fn closed_comparison_admits_only_literal_operands() {
    let mut exec = authored("(set-logic ALL)\n(declare-const k (_ BitVec 8))\n");
    let terms = &mut exec.ctx.terms;
    let four = terms.mk_bitvec(4u32.into(), 8);
    let five = terms.mk_bitvec(5u32.into(), 8);
    let sort = terms.sort(four).clone();
    let k = terms.mk_var("k", sort);
    let closed = terms.mk_app(Symbol::named("bvult"), [four, five], Sort::Bool);
    let negated = terms.mk_not_raw(closed);
    let open = terms.mk_app(Symbol::named("bvult"), [k, five], Sort::Bool);
    let signed = terms.mk_app(Symbol::named("bvslt"), [four, five], Sort::Bool);
    assert!(closed_comparison_over_literals(terms, closed));
    assert!(closed_comparison_over_literals(terms, negated));
    assert!(!closed_comparison_over_literals(terms, open));
    assert!(
        !closed_comparison_over_literals(terms, signed),
        "carcara 1.1.0 misreads negative signed operands"
    );
}
