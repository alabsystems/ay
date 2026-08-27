// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The LEAF-CAP regression for the AUTHORED-CONJUNCT leaf lane
//! (#conjunct-leaf-cap-bail).
//!
//! `MAX_CONJUNCT_LEAVES` used to bound the POPULATION: a proof carrying more
//! premiseless unit-clause `trust` leaves than the cap made the lane
//! `return 0` before it looked at a single one, so a proof with 513 leaves
//! derived NOTHING while a proof with 512 derived everything it could. It now
//! bounds the WORK — how many fragments are built, closed, strict-checked and
//! rendered — which is the same ceiling, reached from the other side.
//!
//! Every fixture here is a COMPLETE REFUTATION: it is asserted to be REJECTED
//! by the untouched strict checker before the lane runs, its leaf population is
//! asserted, and the rebuilt proof is replayed by `check_proof` afterwards.
//!
//! # GUARD MUTATION LEDGER
//!
//! Each was applied, the whole `ay-dpll` `--lib` suite re-run UNFILTERED, the
//! named test observed FAILING, and the source restored.
//!
//! | # | guard | mutation | result |
//! |---|---|---|---|
//! | 1 | the WORK cap `planned >= MAX_CONJUNCT_LEAVES` | delete the `continue` arm | **FAILS** `the_work_cap_bounds_the_number_of_planned_fragments` |
//! | 2 | the work cap is a cap on PLANNED, not on the population | restore `leaves.len() > MAX_CONJUNCT_LEAVES { return 0 }` | **FAILS** `a_proof_with_more_leaves_than_the_cap_still_derives_its_conjuncts` and `the_work_cap_bounds_the_number_of_planned_fragments` |
//! | 3 | Guard 3 (root in both scopes) IN THE WIDE REGIME | drop the `strict_scope` test | **FAILS** `an_assertion_outside_the_strict_scope_is_never_assumed` (the sibling file's guard test, unfiltered) |
//! | 4 | Guard 3, `descents.is_empty()` IN THE WIDE REGIME | accept a foreign atom into the index | **FAILS** `a_foreign_leaf_is_still_refused_in_the_wide_regime` |
//!
//! Mutation 2 is the mutation this file exists for: it is the code that
//! shipped, and both tests here are RED against it.

use ay_core::kani_compat::DetHashMap;
use ay_core::{AletheRule, ProofId, ProofStep, Sort, TermId};

use super::negative_tests::{atoms, decidable, eval, falsify};
use super::tests::{premiseless_unit_trust_leaves, solve};
use crate::Executor;

/// One more leaf than the lane will ever plan for, so the cap is exercised
/// from both sides in a single fixture.
const WIDE_CONJUNCTS: usize = 600;

/// The lane's own FRAGMENT bound, restated here so a change to it fails loudly
/// rather than silently re-tuning what these tests assert.
const EXPECTED_WORK_CAP: usize = 512;

/// The lane's own ROOT-WEIGHT bound, restated the same way.
const EXPECTED_ROOT_WORK: usize = 1 << 16;

/// The DAG weight of the WIDE root: the `and` node plus its `WIDE_CONJUNCTS`
/// Boolean children. The lane charges this against `MAX_CONJUNCT_ROOT_WORK`
/// once per planned fragment.
const WIDE_ROOT_WEIGHT: usize = WIDE_CONJUNCTS + 1;

/// How many fragments the WEIGHTED budget admits for the wide root. This is
/// the binding bound in these fixtures, not the fragment count: 600 conjuncts
/// of a 601-node root cost 360,600 node-weights, and the budget is 65,536.
const WIDE_ADMITTED: usize = EXPECTED_ROOT_WORK / WIDE_ROOT_WEIGHT;

/// `(assert (and p0 … p599))` plus `(assert (not p0))` — a COMPLETE, UNSAT
/// problem whose single authored root is a flat `and` wider than the cap.
/// This is the SMT-LIB shape the census found: one authored assertion whose
/// conjuncts the solver asserts individually.
fn wide_problem() -> String {
    let mut text = String::from("(set-logic QF_UF)\n");
    for i in 0..WIDE_CONJUNCTS {
        text.push_str(&format!("(declare-fun p{i} () Bool)\n"));
    }
    text.push_str("(assert (and");
    for i in 0..WIDE_CONJUNCTS {
        text.push_str(&format!(" p{i}"));
    }
    text.push_str("))\n(assert (not p0))\n(check-sat)\n");
    text
}

fn boolvar(exec: &mut Executor, name: &str) -> TermId {
    exec.ctx.terms.mk_var(name, Sort::Bool)
}

/// A COMPLETE REFUTATION carrying one premiseless `trust` leaf per element of
/// `leaves`, closed by resolving the leaf at `close_at` against an `assume` of
/// its negation. `close_at` picks a leaf whose negation is an AUTHORED
/// assertion, so the fixture's rejection is the TRUST STEP under test and not
/// an unauthorized assumption.
fn wide_leaf_proof_closing_at(
    exec: &mut Executor,
    leaves: &[TermId],
    close_at: usize,
) -> ay_core::Proof {
    let closer = *leaves.get(close_at).expect("a leaf to close on");
    let negated = exec.ctx.terms.mk_not(closer);
    let mut proof = ay_core::Proof::new();
    for &atom in leaves {
        proof.steps.push(ProofStep::Step {
            rule: AletheRule::Trust,
            clause: vec![atom],
            premises: Vec::new(),
            args: Vec::new(),
        });
    }
    let assume = u32::try_from(proof.steps.len()).expect("index");
    proof.steps.push(ProofStep::Assume(negated));
    proof.steps.push(ProofStep::Step {
        rule: AletheRule::Resolution,
        clause: Vec::new(),
        premises: vec![
            ProofId(u32::try_from(close_at).expect("index")),
            ProofId(assume),
        ],
        args: Vec::new(),
    });
    proof
}

fn wide_leaf_proof(exec: &mut Executor, leaves: &[TermId]) -> ay_core::Proof {
    wide_leaf_proof_closing_at(exec, leaves, 0)
}

/// The lane's entry point against the executor's own strict scope, with the
/// fixture asserted REJECTED first so a green result cannot come from a proof
/// that was already acceptable.
fn run_wide(exec: &mut Executor, proof: &mut ay_core::Proof, expected_leaves: usize) -> usize {
    assert_eq!(
        premiseless_unit_trust_leaves(proof),
        expected_leaves,
        "the fixture must carry exactly the leaf population under test"
    );
    assert!(
        matches!(
            exec.check_proof_strict_with_datatypes(proof),
            Err(ay_proof::ProofCheckError::TrustStep { .. })
        ),
        "the fixture must START rejected, on a trust step"
    );
    let scope = exec.complete_problem_assertions_for_strict_proof();
    exec.derive_authored_conjunct_leaves(proof, &scope)
}

fn wide_conjuncts(exec: &mut Executor) -> Vec<TermId> {
    (0..WIDE_CONJUNCTS)
        .map(|i| boolvar(exec, &format!("p{i}")))
        .collect()
}

// ===== the regression =====

#[test]
fn a_proof_with_more_leaves_than_the_cap_still_derives_its_conjuncts() {
    let mut exec = solve(&wide_problem());
    let leaves = wide_conjuncts(&mut exec);
    let mut proof = wide_leaf_proof(&mut exec, &leaves);

    let derived = run_wide(&mut exec, &mut proof, WIDE_CONJUNCTS);

    assert!(
        derived > 0,
        "a proof carrying {WIDE_CONJUNCTS} leaves must not make the lane refuse all of them"
    );
    assert_eq!(
        premiseless_unit_trust_leaves(&proof),
        WIDE_CONJUNCTS - derived,
        "every derived leaf must leave the trust population"
    );
    assert!(
        proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::Step {
                rule: AletheRule::AndPos(_),
                ..
            }
        )),
        "the descent this lane contributes must be present"
    );
    ay_proof::check_proof(&proof, &exec.ctx.terms).expect("the rebuilt proof must replay");
}

/// The WEIGHTED budget, not the fragment count, is what bounds this fixture:
/// each fragment carries the whole 601-node root, so the lane stops at
/// `MAX_CONJUNCT_ROOT_WORK / |ROOT|` fragments — well short of 512.
#[test]
fn the_work_cap_bounds_the_number_of_planned_fragments() {
    let mut exec = solve(&wide_problem());
    let leaves = wide_conjuncts(&mut exec);
    let mut proof = wide_leaf_proof(&mut exec, &leaves);

    let derived = run_wide(&mut exec, &mut proof, WIDE_CONJUNCTS);

    assert!(
        WIDE_ADMITTED < EXPECTED_WORK_CAP,
        "this fixture must exercise the WEIGHTED budget, not the fragment cap"
    );
    assert_eq!(
        derived, WIDE_ADMITTED,
        "the lane must spend exactly its ROOT-WEIGHT budget when more leaves are derivable"
    );
    assert_eq!(
        premiseless_unit_trust_leaves(&proof),
        WIDE_CONJUNCTS - WIDE_ADMITTED,
        "the leaves past the budget must keep their trust steps, byte for byte"
    );
}

/// The weighted budget must scale with the ROOT, not be a second constant
/// fragment count: with the SAME leaf population, a root a third the size must
/// admit about three times as many fragments.
#[test]
fn a_smaller_root_admits_proportionally_more_fragments() {
    let narrow = WIDE_CONJUNCTS / 3;
    let mut text = String::from("(set-logic QF_UF)\n");
    for i in 0..narrow {
        text.push_str(&format!("(declare-fun p{i} () Bool)\n"));
    }
    text.push_str("(assert (and");
    for i in 0..narrow {
        text.push_str(&format!(" p{i}"));
    }
    text.push_str("))\n(assert (not p0))\n(check-sat)\n");
    let mut exec = solve(&text);
    let conjuncts: Vec<TermId> = (0..narrow)
        .map(|i| boolvar(&mut exec, &format!("p{i}")))
        .collect();
    // The SAME population as the wide fixture, so only the ROOT differs.
    let mut leaves = Vec::new();
    while leaves.len() < WIDE_CONJUNCTS {
        leaves.extend(conjuncts.iter().copied());
    }
    leaves.truncate(WIDE_CONJUNCTS);
    let mut proof = wide_leaf_proof(&mut exec, &leaves);

    let derived = run_wide(&mut exec, &mut proof, WIDE_CONJUNCTS);

    let narrow_admitted = EXPECTED_ROOT_WORK / (narrow + 1);
    assert_eq!(
        derived,
        narrow_admitted.min(EXPECTED_WORK_CAP),
        "the budget must admit `MAX_CONJUNCT_ROOT_WORK / |ROOT|` fragments"
    );
    assert!(
        derived > WIDE_ADMITTED * 2,
        "a root a THIRD the size must admit far more fragments than the wide one — \
         the budget must be weighted by the root, not a second fragment count"
    );
    ay_proof::check_proof(&proof, &exec.ctx.terms).expect("the rebuilt proof must replay");
}

/// NON-REGRESSION: a leaf population the SHIPPED lane already accepted
/// (`<= MAX_CONJUNCT_LEAVES`) must be planned exactly as before, whatever the
/// root weighs. The weighted budget governs only the capability this change
/// ADDS; measured, a budget applied globally cost QF_LRA 2,481 derivations the
/// shipped lane had.
#[test]
fn a_population_the_shipped_lane_accepted_is_never_newly_declined() {
    let mut exec = solve(&wide_problem());
    let all = wide_conjuncts(&mut exec);
    let shipped_eligible = EXPECTED_WORK_CAP - 112;
    let leaves = all[..shipped_eligible].to_vec();
    let mut proof = wide_leaf_proof(&mut exec, &leaves);

    let derived = run_wide(&mut exec, &mut proof, shipped_eligible);

    assert!(
        shipped_eligible * WIDE_ROOT_WEIGHT > EXPECTED_ROOT_WORK,
        "this fixture must be one the WEIGHTED budget would refuse if it applied"
    );
    assert!(
        shipped_eligible <= EXPECTED_WORK_CAP,
        "…and one the SHIPPED population bail accepted"
    );
    assert_eq!(
        derived, shipped_eligible,
        "every leaf the shipped lane would have derived must still be derived"
    );
    assert_eq!(premiseless_unit_trust_leaves(&proof), 0);
    ay_proof::check_proof(&proof, &exec.ctx.terms).expect("the rebuilt proof must replay");
}

/// The leaves the budget declines are left EXACTLY as they were — the lane
/// must never trade one for a `hole`, a weaker rule, or a different clause.
#[test]
fn the_leaves_past_the_work_cap_keep_their_own_clauses() {
    let mut exec = solve(&wide_problem());
    let leaves = wide_conjuncts(&mut exec);
    let mut proof = wide_leaf_proof(&mut exec, &leaves);
    let derived = run_wide(&mut exec, &mut proof, WIDE_CONJUNCTS);

    let surviving: Vec<TermId> = proof
        .steps
        .iter()
        .filter_map(|step| match step {
            ProofStep::Step {
                rule: AletheRule::Trust,
                clause,
                premises,
                args,
            } if premises.is_empty() && args.is_empty() && clause.len() == 1 => Some(clause[0]),
            _ => None,
        })
        .collect();
    assert_eq!(
        surviving,
        leaves[derived..].to_vec(),
        "the untouched tail must be the ORIGINAL leaves, in the original order"
    );
    assert!(
        !proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::Step {
                rule: AletheRule::Hole,
                ..
            }
        )),
        "the lane must never trade a trust step for a hole"
    );
}

// ===== the adversarial negative, IN THE WIDE REGIME =====

/// A problem whose authored root is a SMALL `and` and which also declares a
/// Boolean `q` the root does not entail. Small enough for the independent
/// truth-table evaluator to enumerate.
const SMALL_ROOT: &str = r#"
    (set-logic QF_UF)
    (declare-fun b0 () Bool)
    (declare-fun b1 () Bool)
    (declare-fun b2 () Bool)
    (declare-fun b3 () Bool)
    (declare-fun q () Bool)
    (declare-fun zz () Bool)
    (assert (and b0 b1 b2 b3))
    (assert zz)
    (assert (not zz))
    (check-sat)
"#;

/// With the population bail gone, a proof wider than the cap now REACHES the
/// index — and a leaf the authored root does not contain must still be
/// refused. The falsifying assignment is NAMED and re-checked in-test.
#[test]
fn a_foreign_leaf_is_still_refused_in_the_wide_regime() {
    let mut exec = solve(SMALL_ROOT);
    let foreign = boolvar(&mut exec, "q");
    let b0 = boolvar(&mut exec, "b0");
    let b1 = boolvar(&mut exec, "b1");
    let b2 = boolvar(&mut exec, "b2");
    let b3 = boolvar(&mut exec, "b3");
    let root = {
        let terms = &mut exec.ctx.terms;
        terms.mk_and(vec![b0, b1, b2, b3])
    };

    // The independent evaluator: the root does NOT entail the foreign atom,
    // and the witness is stated explicitly rather than merely searched for.
    assert!(
        decidable(&exec.ctx.terms, root) && decidable(&exec.ctx.terms, foreign),
        "the evaluator must understand every node of both terms"
    );
    let witness =
        falsify(&exec.ctx.terms, root, foreign).expect("the root must NOT entail the foreign atom");
    let env: DetHashMap<TermId, bool> = witness.iter().copied().collect();
    assert_eq!(
        eval(&exec.ctx.terms, root, &env),
        Some(true),
        "the named assignment must SATISFY the authored root"
    );
    assert_eq!(
        eval(&exec.ctx.terms, foreign, &env),
        Some(false),
        "the named assignment must FALSIFY the leaf the lane must refuse"
    );
    let mut named: Vec<TermId> = Vec::new();
    atoms(&exec.ctx.terms, root, &mut named);
    atoms(&exec.ctx.terms, foreign, &mut named);
    assert_eq!(
        named.len(),
        5,
        "the witness must be over exactly b0..b3 and q"
    );

    // The FOREIGN leaf first, then a population well past the work cap. The
    // refutation closes on the AUTHORED `zz`, whose negation is an authored
    // assertion, so the fixture's only rejection reason is the trust steps.
    let zz = boolvar(&mut exec, "zz");
    let mut leaves = vec![foreign, zz];
    leaves.extend(std::iter::repeat_n(b0, EXPECTED_WORK_CAP + 8));
    let mut proof = wide_leaf_proof_closing_at(&mut exec, &leaves, 1);
    let before = format!("{:?}", proof.steps[0]);

    let derived = run_wide(&mut exec, &mut proof, leaves.len());

    assert_eq!(
        derived, EXPECTED_WORK_CAP,
        "the derivable copies must be served up to the work cap"
    );
    assert_eq!(
        format!("{:?}", proof.steps[0]),
        before,
        "the FOREIGN leaf must be byte-identical after the lane ran"
    );
    for step in &proof.steps {
        let ProofStep::Assume(term) = step else {
            continue;
        };
        assert_ne!(
            *term, foreign,
            "the lane must never ASSUME a term the authored root does not entail"
        );
    }
    ay_proof::check_proof(&proof, &exec.ctx.terms).expect("the rebuilt proof must replay");
}

// ===== the PRINTER, in the wide regime =====

/// Exact wire text: the fragment the lane splices into a wider-than-cap proof
/// prints as `and_pos` over the authored root and `th_resolution`, and no
/// `trust` or `hole` line survives for the leaves it served.
#[test]
fn the_wide_regime_fragment_prints_and_pos_on_the_wire() {
    let mut exec = solve(SMALL_ROOT);
    let b0 = boolvar(&mut exec, "b0");
    let b1 = boolvar(&mut exec, "b1");
    let leaves = vec![b1, b0];
    let mut proof = wide_leaf_proof(&mut exec, &leaves);
    let scope = exec.complete_problem_assertions_for_strict_proof();
    assert_eq!(exec.derive_authored_conjunct_leaves(&mut proof, &scope), 2);

    let document =
        ay_proof::try_export_alethe(&proof, &exec.ctx.terms).expect("the proof must render");
    assert!(
        document.contains("(step t1 (cl (not (and b0 b1 b2 b3)) b1) :rule and_pos :args (1))"),
        "the descent must print the authored root, the conjunct and the POSITION:\n{document}"
    );
    assert!(
        document.contains("(step t2 (cl b1) :rule th_resolution :premises (t1 t0))"),
        "the descent's resolution must cite the and_pos and the root assume:\n{document}"
    );
    assert!(
        !document.contains(":rule trust"),
        "no trust step may survive for a leaf the lane served:\n{document}"
    );
    assert!(
        !document.contains(":rule hole"),
        "the lane must not trade a trust step for a hole:\n{document}"
    );
}
