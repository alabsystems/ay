// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unit pins for the implied-universal ground-instantiation lane.

use super::*;
use crate::executor::Executor;

/// `(assert p)` and `(assert (=> p (forall ((x Int)) (> x 10))))` with the
/// authored ground fact `(< a 0)`: the body normalizes to `(< 10 x)`, so the
/// binder's argument slot is `<` position 1, the authored `(< a 0)` puts the
/// numeral `0` in that slot, and the planned instance `(< 10 0)` is an
/// arithmetic falsehood that closes the refutation on its own.
///
/// The ground fact is deliberately an INEQUALITY, not a literal-valued
/// equality: a value pin would route the refutation through
/// `try_distinct_ground_pin`, whose `GroundEqualitySubstitution` kind AY's own
/// strict checker accepts but the Alethe printer must spell `hole`. An
/// inequality forces the same-context probe route, whose every step has a
/// checked wire spelling — which is what lets this test pin exact wire text.
fn implied_forall_conflict_executor() -> Executor {
    let commands = ay_frontend::parse(
        r#"
            (set-logic AUFLIA)
            (declare-const p Bool)
            (declare-const a Int)
            (assert p)
            (assert (=> p (forall ((x Int)) (> x 10))))
            (assert (< a 0))
        "#,
    )
    .expect("implied-forall fixture parses");
    let mut exec = Executor::new();
    assert!(
        exec.execute_all(&commands)
            .expect("implied-forall fixture loads")
            .is_empty(),
        "fixture must contain declarations and assertions only"
    );
    exec.begin_unsat_query_epoch(&exec.ctx.assertions.clone());
    exec.bind_unsat_query_assumptions(&[]);
    exec
}

/// The lane BUILDS the artifact: the universal is reachable only through the
/// implication, so no `forall_inst` record exists for it, and only the
/// `implies_pos` prologue can derive it.
///
/// MUTATION: drop the `ImpliedConsequent` arm from `planned_consequence_unit`
/// (return `None`), or make `plan_implied_foralls` return an empty set, and
/// this fails.
#[test]
fn an_implied_universal_is_instantiated_through_an_implies_pos_prologue() {
    let mut exec = implied_forall_conflict_executor();
    assert!(
        exec.try_translate_implied_forall_ground_instantiation_unsat(),
        "the universal under `(=> p ...)` at x := 0 is an arithmetic falsehood"
    );
    let proof = exec
        .last_proof
        .clone()
        .expect("translation installs last_proof");
    assert!(
        proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::Step {
                rule: AletheRule::ImpliesPos,
                ..
            }
        )),
        "the stitched proof reaches the universal by implies_pos"
    );
    assert!(
        proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::Step {
                rule: AletheRule::ForallInst,
                ..
            }
        )),
        "the stitched proof derives the instance by forall_inst"
    );
    let quality = exec
        .check_proof_strict_with_datatypes(&proof)
        .expect("the stitched proof is strictly checkable");
    assert!(
        quality.is_complete(),
        "no trust and no hole may survive: {quality:?}"
    );
    let authored = exec.exact_concrete_authored_scope();
    assert!(ay_proof::validate_reachable_assumes_in_problem_scope(&proof, &authored).is_ok());
    let alethe = ay_proof::try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &exec.ctx.terms,
        &authored,
        None,
    )
    .expect("Alethe export must succeed");
    // EXACT WIRE TEXT. The `implies_pos` prologue (t3-t5) is the new
    // capability: it derives the universal from an authored implication and its
    // authored antecedent, which no `and`-spine provenance path could reach.
    // Every rule here is in `CHECKABLE_ALETHE_RULES` with a strict validator —
    // no `trust`, no `hole`.
    assert_eq!(
        alethe,
        concat!(
            "(assume t0 (or (forall ((x_2 Int)) (< 10 x_2)) (not p)))\n",
            "(assume t1 p)\n",
            "(step t2 (cl (not (or (forall ((x_2 Int)) (< 10 x_2)) (not p))) (not p) ",
            "(forall ((x_2 Int)) (< 10 x_2))) :rule implies_pos)\n",
            "(step t3 (cl (not p) (forall ((x_2 Int)) (< 10 x_2))) :rule resolution ",
            ":premises (t2 t0))\n",
            "(step t4 (cl (forall ((x_2 Int)) (< 10 x_2))) :rule resolution :premises (t3 t1))\n",
            "(step t5 (cl (or (not (forall ((x_2 Int)) (< 10 x_2))) (< 10 0))) :rule forall_inst ",
            ":args (0))\n",
            "(step t6 (cl (not (forall ((x_2 Int)) (< 10 x_2))) (< 10 0)) :rule or :premises (t5))\n",
            "(step t7 (cl (< 10 0)) :rule resolution :premises (t6 t4))\n",
            "(step t8 (cl (not (< 10 0))) :rule la_generic :args (1))\n",
            "(step t9 (cl) :rule th_resolution :premises (t8 t7))\n",
        ),
        "the emitted Alethe document changed"
    );
    assert!(
        !alethe.contains(":rule trust") && !alethe.contains(":rule hole"),
        "no unchecked rule may survive: {alethe}"
    );
}

/// FAILS CLOSED when the antecedent is NOT an authored root: `(=> q F)` with
/// `q` never asserted leaves `F` un-entailed, so no instance may be proposed.
///
/// MUTATION STATUS, MEASURED: dropping the
/// `authored_set.contains(&antecedent)` guard in
/// `exact_authored_implied_forall_roots` does NOT redden this test, and
/// neither does additionally dropping the
/// `derivable_sources.contains(&implied.antecedent)` re-check in
/// `plan_implied_foralls` — the stitcher's `consequence_unit` still has to
/// DERIVE `(cl antecedent)` from the authored scope and fails closed. This
/// test therefore pins the fail-closed STACK, not one guard; the capability
/// mutation with a verified red lives on the sibling positive test.
#[test]
fn an_unasserted_antecedent_proposes_nothing() {
    let commands = ay_frontend::parse(
        r#"
            (set-logic AUFLIA)
            (declare-const q Bool)
            (declare-const a Int)
            (assert (=> q (forall ((x Int)) (> x 10))))
            (assert (< a 0))
        "#,
    )
    .expect("unasserted-antecedent fixture parses");
    let mut exec = Executor::new();
    assert!(exec
        .execute_all(&commands)
        .expect("fixture loads")
        .is_empty());
    exec.begin_unsat_query_epoch(&exec.ctx.assertions.clone());
    exec.bind_unsat_query_assumptions(&[]);
    assert!(
        !exec.try_translate_implied_forall_ground_instantiation_unsat(),
        "an un-entailed universal must propose no instance"
    );
    assert!(exec.last_proof.is_none());
}

/// The attempt budget is enforced: the identical executor translates with a
/// fresh budget (sibling test above), and an exhausted one declines without
/// touching proof state.
#[test]
fn the_lane_attempt_budget_is_enforced() {
    let mut exec = implied_forall_conflict_executor();
    exec.implied_forall_ground_inst_attempts
        .set(MAX_LANE_ATTEMPTS);
    assert!(!exec.try_translate_implied_forall_ground_instantiation_unsat());
    assert!(exec.last_proof.is_none());
}

/// FALSIFY ONCE. Plant the byte-identical derivation shape over a
/// SATISFIABLE instance — same authored implication, same `implies_pos`
/// prologue, same `forall_inst` at the same witness — and show the UNTOUCHED
/// strict checker refuses it.
///
/// The universal is `(> x (- 10))` and the ground fact is `(< a 0)`, so
/// `a = -5` satisfies both and no empty clause exists. The lane must
/// decline, and a hand-built candidate that stops at the instance must fail
/// the empty-clause gate rather than being admitted as a refutation.
#[test]
fn the_same_derivation_over_a_satisfiable_instance_is_refused() {
    let commands = ay_frontend::parse(
        r#"
            (set-logic AUFLIA)
            (declare-const p Bool)
            (declare-const a Int)
            (assert p)
            (assert (=> p (forall ((x Int)) (> x (- 10)))))
            (assert (< a 0))
        "#,
    )
    .expect("satisfiable twin parses");
    let mut exec = Executor::new();
    assert!(exec
        .execute_all(&commands)
        .expect("satisfiable twin loads")
        .is_empty());
    exec.begin_unsat_query_epoch(&exec.ctx.assertions.clone());
    exec.bind_unsat_query_assumptions(&[]);
    assert!(
        !exec.try_translate_implied_forall_ground_instantiation_unsat(),
        "a satisfiable consequence set must not yield an installed refutation"
    );
    assert!(
        exec.last_proof.is_none(),
        "a declined translation leaves proof state as found"
    );

    // And the derivation itself, built by hand over the same roots, does not
    // derive the empty clause — the property the installation boundary checks
    // before the strict checker even runs.
    let authored = exec.exact_concrete_authored_scope();
    let implication = *authored
        .iter()
        .find(|&&root| {
            Executor::decode_implication_local(&exec.ctx.terms, root).is_some_and(
                |(_, consequent)| matches!(exec.ctx.terms.get(consequent), TermData::Forall(..)),
            )
        })
        .expect("the twin keeps the implication root");
    let (antecedent, forall) =
        Executor::decode_implication_local(&exec.ctx.terms, implication).expect("decoded above");
    let mut candidate = Proof::new();
    let implication_unit = candidate.add_assume(implication, None);
    let antecedent_unit = candidate.add_assume(antecedent, None);
    let forall_unit = exec.apply_implication_unit(
        &mut candidate,
        implication,
        implication_unit,
        antecedent,
        antecedent_unit,
        forall,
    );
    let _ = forall_unit;
    assert!(
        !Executor::proof_derives_empty_clause(&candidate),
        "a derivation over a satisfiable instance reaches no empty clause"
    );
}
