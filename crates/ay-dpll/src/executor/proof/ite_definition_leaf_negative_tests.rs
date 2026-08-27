// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! ADVERSARIAL negatives for the ITE-definition leaf lane, each naming a
//! concrete falsifying assignment and CHECKING it in-test with an INDEPENDENT
//! evaluator that shares no code with the emitter or with `ay_proof`, plus an
//! exhaustive sweep whose every ACCEPT is re-checked by that evaluator.
//!
//! The one inference this lane contributes beyond existing validators is the
//! composition
//!
//! ```text
//!   d = I            (the minted definition)
//!   G ∨ (I = b)      (ite_branch_projection)
//!   ---------------
//!   G ∨ (d = b)      and, packed, `(or G (= d b))`
//! ```
//!
//! so the sweep enumerates every assignment to the ite's condition and to the
//! two branch values over a small finite domain, evaluates the emitted or-term
//! under the minted definition, and asserts it is TRUE — and separately that
//! the MIRROR clause (the other branch) is FALSE somewhere, so the sweep is
//! not vacuous.

use ay_core::{AletheRule, ProofStep, Sort, TermData, TermId, TermStore};

use super::super::super::Executor;
use super::tests::{
    fixture, leaf_proof, negative_half, premiseless_unit_trust_leaves, rerun, Fixture,
};

// ===== an INDEPENDENT evaluator, sharing no code with the emitter =====

/// A tiny total interpretation: `condition -> bool`, `Int var -> i64`.
#[derive(Clone, Copy)]
struct Model {
    condition: bool,
    definiendum: i64,
}

/// Evaluate the leaf's or-term under `model` PLUS the minted definition
/// `d = ite(c, t, e)`. Returns `None` for any shape this evaluator does not
/// model, which the caller treats as a test failure rather than a pass.
fn evaluate(
    terms: &TermStore,
    term: TermId,
    condition: TermId,
    definiendum: TermId,
    model: Model,
) -> Option<bool> {
    match terms.get(term) {
        TermData::Not(inner) => Some(!evaluate(terms, *inner, condition, definiendum, model)?),
        TermData::App(symbol, args) if symbol.name() == "or" => {
            let mut value = false;
            for &arg in args {
                value |= evaluate(terms, arg, condition, definiendum, model)?;
            }
            Some(value)
        }
        TermData::App(symbol, args) if symbol.name() == "=" && args.len() == 2 => {
            let left = evaluate_int(terms, args[0], definiendum, model)?;
            let right = evaluate_int(terms, args[1], definiendum, model)?;
            Some(left == right)
        }
        _ if term == condition => Some(model.condition),
        _ => None,
    }
}

fn evaluate_int(terms: &TermStore, term: TermId, definiendum: TermId, model: Model) -> Option<i64> {
    if term == definiendum {
        return Some(model.definiendum);
    }
    match terms.get(term) {
        TermData::Const(ay_core::term::Constant::Int(value)) => i64::try_from(value).ok(),
        _ => None,
    }
}

/// The value the MINTED definition forces on `d`.
fn definition_value(condition: bool, then_value: i64, else_value: i64) -> i64 {
    if condition {
        then_value
    } else {
        else_value
    }
}

// ===== the falsifying assignments =====

#[test]
fn the_mismatched_branch_clause_is_refuted_by_a_named_assignment() {
    // `(or (not c) (= d 0))` under `d := (ite c 1 0)` is FALSE at c = true,
    // where the definition forces d = 1 and `0 = 1` fails.
    let mut f = fixture();
    let equality = f.exec.ctx.terms.mk_eq(f.definiendum, f.else_branch);
    let not_condition = f.exec.ctx.terms.mk_not(f.condition);
    let goal = f.exec.ctx.terms.mk_or(vec![not_condition, equality]);
    let model = Model {
        condition: true,
        definiendum: definition_value(true, 1, 0),
    };
    assert_eq!(
        evaluate(&f.exec.ctx.terms, goal, f.condition, f.definiendum, model),
        Some(false),
        "the named assignment must REFUTE the mismatched-branch clause"
    );
    let mut proof = leaf_proof(&mut f.exec, goal);
    assert_eq!(
        rerun(&mut f.exec, &mut proof),
        0,
        "and the lane must decline it"
    );
    assert_eq!(premiseless_unit_trust_leaves(&proof), 2);
}

#[test]
fn the_unguarded_equality_is_refuted_by_a_named_assignment() {
    // `(or unrelated (= d 1))` under `d := (ite c 1 0)` is FALSE at
    // c = false, unrelated = false: d = 0 and `0 = 1` fails.
    let mut f = fixture();
    let equality = f.exec.ctx.terms.mk_eq(f.definiendum, f.then_branch);
    let unrelated = f.exec.ctx.terms.mk_var("itedef_other", Sort::Bool);
    let goal = f.exec.ctx.terms.mk_or(vec![unrelated, equality]);
    // The evaluator models only `condition`; `unrelated` is a DIFFERENT
    // variable, so pass it as the condition slot set to false.
    let model = Model {
        condition: false,
        definiendum: definition_value(false, 1, 0),
    };
    assert_eq!(
        evaluate(&f.exec.ctx.terms, goal, unrelated, f.definiendum, model),
        Some(false),
        "the named assignment must REFUTE the unguarded clause"
    );
    let mut proof = leaf_proof(&mut f.exec, goal);
    assert_eq!(rerun(&mut f.exec, &mut proof), 0);
}

// ===== the exhaustive sweep =====

/// Every `(condition polarity, then value, else value)` over a small domain:
/// the lane's ACCEPT is re-checked by the independent evaluator, under BOTH
/// truth values of the condition, and its DECLINE is re-checked to be a clause
/// the evaluator can actually refute.
#[test]
fn every_accept_is_true_under_every_assignment_and_every_decline_is_refutable() {
    let mut accepts = 0usize;
    let mut declines = 0usize;
    for then_value in -2i64..=2 {
        for else_value in -2i64..=2 {
            for guard_negative in [true, false] {
                for use_then_branch in [true, false] {
                    let mut f = build(then_value, else_value);
                    let branch = if use_then_branch {
                        f.then_branch
                    } else {
                        f.else_branch
                    };
                    let equality = f.exec.ctx.terms.mk_eq(f.definiendum, branch);
                    let guard = if guard_negative {
                        f.exec.ctx.terms.mk_not(f.condition)
                    } else {
                        f.condition
                    };
                    let goal = f.exec.ctx.terms.mk_or(vec![guard, equality]);
                    // `mk_or`/`mk_eq` may fold when the two branch values
                    // coincide; only a genuine binary `or` is in scope.
                    let binary_or = matches!(
                        f.exec.ctx.terms.get(goal),
                        TermData::App(symbol, args) if symbol.name() == "or" && args.len() == 2
                    );
                    if !binary_or {
                        continue;
                    }
                    let mut proof = leaf_proof(&mut f.exec, goal);
                    let derived = rerun(&mut f.exec, &mut proof);
                    if derived == 1 {
                        accepts += 1;
                        for condition in [true, false] {
                            let model = Model {
                                condition,
                                definiendum: definition_value(condition, then_value, else_value),
                            };
                            assert_eq!(
                                evaluate(
                                    &f.exec.ctx.terms,
                                    goal,
                                    f.condition,
                                    f.definiendum,
                                    model
                                ),
                                Some(true),
                                "ACCEPTED clause is false at condition = {condition}, \
                                 then = {then_value}, else = {else_value}, \
                                 guard_negative = {guard_negative}, \
                                 use_then_branch = {use_then_branch}"
                            );
                        }
                        // And the finished proof's only trust step is the
                        // fixture's own closer.
                        assert_eq!(premiseless_unit_trust_leaves(&proof), 1);
                    } else {
                        assert_eq!(derived, 0);
                        declines += 1;
                    }
                }
            }
        }
    }
    assert!(
        accepts >= 20,
        "the sweep must exercise accepts, got {accepts}"
    );
    assert!(
        declines >= 10,
        "the sweep must exercise declines, got {declines}"
    );
}

/// A fixture over chosen branch values.
fn build(then_value: i64, else_value: i64) -> Fixture {
    let mut exec = Executor::new();
    let terms = &mut exec.ctx.terms;
    let condition = terms.mk_var("itedef_c", Sort::Bool);
    let then_branch = terms.mk_int(then_value.into());
    let else_branch = terms.mk_int(else_value.into());
    let ite = terms.mk_ite_raw(condition, then_branch, else_branch);
    let sort = terms.sort(ite).clone();
    let definiendum = terms.mk_var(format!("__ay_ite_def_{}", ite.0), sort);
    let unrelated = terms.mk_var("itedef_unrelated", Sort::Bool);
    exec.ctx.assertions = vec![unrelated];
    Fixture {
        exec,
        condition,
        ite,
        definiendum,
        then_branch,
        else_branch,
    }
}

// ===== the wire =====

/// The exact wire text. `fresh_def_eq` and `ite_branch_projection` are
/// INTERNALLY checked rules with no external Alethe primitive, so both lower to
/// an honest `hole` -- the same convention `minted_definition_leaf` already
/// prints its minted definition under. This lane therefore trades a `:rule
/// trust` for two honest `hole`s plus four externally named rules; it never
/// leaves a `:rule trust` on the wire.
#[test]
fn the_fragment_prints_its_rules_on_the_wire() {
    let mut f = fixture();
    let goal = negative_half(&mut f);
    let mut proof = leaf_proof(&mut f.exec, goal);
    assert_eq!(rerun(&mut f.exec, &mut proof), 1);
    let document = ay_proof::try_export_alethe(&proof, &f.exec.ctx.terms)
        .expect("the finished proof must export");
    assert_eq!(
        document.matches(":rule trust").count(),
        0,
        "no trust step may reach the wire:\n{document}"
    );
    for expected in [
        "(step t0 (cl (= __ay_ite_def_5 (ite itedef_c 1 0))) :rule hole)",
        "(step t1 (cl (not itedef_c) (= (ite itedef_c 1 0) 1)) :rule hole)",
        ":rule eq_transitive",
        ":rule th_resolution",
        ":rule or_neg",
        ":rule contraction",
    ] {
        assert!(
            document.contains(expected),
            "missing `{expected}` on the wire:\n{document}"
        );
    }
    // The minted definition, the ite projection, and the fixture's own closer.
    assert_eq!(
        document.matches(":rule hole").count(),
        3,
        "exactly the two internally-checked leaf steps and the fixture's own closer:\n{document}"
    );
}

#[test]
fn the_lane_writes_no_assume_at_all() {
    let mut f = fixture();
    let goal = negative_half(&mut f);
    let mut proof = leaf_proof(&mut f.exec, goal);
    let before = proof
        .steps
        .iter()
        .filter(|step| matches!(step, ProofStep::Assume(_)))
        .count();
    assert_eq!(rerun(&mut f.exec, &mut proof), 1);
    let after = proof
        .steps
        .iter()
        .filter(|step| matches!(step, ProofStep::Assume(_)))
        .count();
    assert_eq!(
        before, after,
        "this lane assumes NOTHING; it only mints a definition"
    );
    assert!(proof.steps.iter().any(|step| matches!(
        step,
        ProofStep::Step {
            rule: AletheRule::FreshDefEq,
            ..
        }
    )));
}
