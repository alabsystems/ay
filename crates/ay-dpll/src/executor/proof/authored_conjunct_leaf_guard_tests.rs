// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! HAND-BUILT guard fixtures for the AUTHORED-CONJUNCT leaf lane.
//!
//! Split out of `authored_conjunct_leaf_tests.rs` so each file stays inside the
//! repository's 500-line ceiling. That file owns the census-regime END-TO-END
//! solves, the wire check and the shared fixtures; this one owns the guards.
//! The GUARD MUTATION LEDGER, which names the test each mutation turns red,
//! lives in that file.
//!
//! **Every fixture is a COMPLETE REFUTATION** and asserts, before running the
//! lane, that it starts REJECTED and that the leaf this lane claims is present.

use ay_core::{AletheRule, ProofId, ProofStep, Sort, TermId};

use super::tests::{
    first_disequality, last_disequality, leaf_proof, premiseless_unit_trust_leaves, rerun, shape,
    solve, DISTINCT_STORECOMM, NESTED,
};

#[test]
fn a_hand_built_conjunct_leaf_is_derived_and_the_rebuilt_proof_replays() {
    let mut exec = solve(DISTINCT_STORECOMM);
    let atom = first_disequality(&mut exec);
    let mut proof = leaf_proof(&mut exec, atom, Vec::new(), Vec::new());
    // The fixture must start REJECTED and must carry the leaf this lane
    // claims, or it proves nothing.
    assert!(exec.check_proof_strict_with_datatypes(&proof).is_err());
    assert_eq!(premiseless_unit_trust_leaves(&proof), 1);
    assert_eq!(rerun(&mut exec, &mut proof), 1);
    assert_eq!(premiseless_unit_trust_leaves(&proof), 0);
    // The fixture's own `assume (not atom)` is not an authored assertion, so
    // the closed refutation cannot certify outright; what MUST hold is that
    // every step of the derivation replays and the only unauthorised leaf is
    // the one the fixture introduced on purpose.
    match exec.check_proof_strict_with_datatypes(&proof) {
        Ok(_) => {}
        Err(ay_proof::ProofCheckError::UnauthorizedAssumption { .. }) => {}
        Err(other) => panic!("the rebuilt proof must replay, got {other:?}"),
    }
}

#[test]
fn a_conjunct_at_a_later_position_is_derived() {
    let mut exec = solve(DISTINCT_STORECOMM);
    let atom = last_disequality(&mut exec);
    let mut proof = leaf_proof(&mut exec, atom, Vec::new(), Vec::new());
    assert_eq!(premiseless_unit_trust_leaves(&proof), 1);
    assert_eq!(rerun(&mut exec, &mut proof), 1);
    // The emitted `and_pos` must name the position the conjunct actually sits
    // at, which is what `validate_and_pos` re-derives from `:args`.
    let positions: Vec<u32> = proof
        .steps
        .iter()
        .filter_map(|step| match step {
            ProofStep::Step {
                rule: AletheRule::AndPos(position),
                ..
            } => Some(*position),
            _ => None,
        })
        .collect();
    assert_eq!(positions, vec![2], "`(not (= i1 i2))` is conjunct 2");
}

#[test]
fn the_replaced_leaf_keeps_its_clause_byte_for_byte() {
    let mut exec = solve(DISTINCT_STORECOMM);
    let atom = first_disequality(&mut exec);
    let mut proof = leaf_proof(&mut exec, atom, Vec::new(), Vec::new());
    assert_eq!(rerun(&mut exec, &mut proof), 1);
    let ProofStep::Step { premises, .. } = proof.steps.last().expect("a terminal step") else {
        panic!("the terminal step is a resolution");
    };
    let last = premises[0].0 as usize;
    let ProofStep::Step { clause, .. } = &proof.steps[last] else {
        panic!("the fragment ends on a generic step");
    };
    assert_eq!(clause.as_slice(), [atom]);
}

#[test]
fn the_lane_assumes_only_authored_roots() {
    let mut exec = solve(DISTINCT_STORECOMM);
    let atom = first_disequality(&mut exec);
    let mut proof = leaf_proof(&mut exec, atom, Vec::new(), Vec::new());
    let negated = exec.ctx.terms.mk_not(atom);
    assert_eq!(rerun(&mut exec, &mut proof), 1);
    let scope: Vec<TermId> = exec.complete_problem_assertions_for_strict_proof();
    let mut assumed = 0usize;
    for step in &proof.steps {
        let ProofStep::Assume(term) = step else {
            continue;
        };
        if *term == negated {
            continue; // the fixture's own closing assumption
        }
        assumed += 1;
        assert!(
            scope.contains(term),
            "the lane assumed a term outside the strict scope: {term:?}"
        );
    }
    assert_eq!(assumed, 1, "the lane assumes exactly the authored root");
}

#[test]
fn the_closed_fragment_is_replayed_by_the_untouched_strict_checker() {
    let mut exec = solve(DISTINCT_STORECOMM);
    let atom = first_disequality(&mut exec);
    let mut proof = leaf_proof(&mut exec, atom, Vec::new(), Vec::new());
    assert_eq!(rerun(&mut exec, &mut proof), 1);
    // Take the fragment back out of the spliced proof and replay it CLOSED,
    // through the same public entry point the lane's Guard 6 uses.
    let fragment: Vec<ProofStep> = proof.steps[..proof.steps.len() - 2].to_vec();
    let closed = ay_proof::close_congruence_derivation(
        &mut exec.ctx.terms,
        &ay_proof::CongruenceDerivation {
            steps: fragment,
            clause: vec![atom],
        },
    );
    ay_proof::check_proof_strict(&closed, &exec.ctx.terms)
        .expect("the closed fragment must replay under the untouched strict checker");
}

/// MEASURED, and it is why mutation 11 is an honest negative: `mk_and`
/// FLATTENS nested `and` applications (`ay-core/src/term/boolean.rs`, the
/// `TermData::App(and, ..)` arm), sorts and dedups, so an AUTHORED assertion
/// can never nest one `and` inside another. Every one of the 14 corpus
/// instances is at nesting depth 1 for exactly this reason.
#[test]
fn a_flattened_authored_and_puts_every_conjunct_at_depth_one() {
    let mut exec = solve(NESTED);
    let r = exec.ctx.terms.mk_var("r", Sort::Bool);
    let mut proof = leaf_proof(&mut exec, r, Vec::new(), Vec::new());
    assert!(exec.check_proof_strict_with_datatypes(&proof).is_err());
    assert_eq!(premiseless_unit_trust_leaves(&proof), 1);
    assert_eq!(rerun(&mut exec, &mut proof), 1);
    let positions: Vec<u32> = proof
        .steps
        .iter()
        .filter_map(|step| match step {
            ProofStep::Step {
                rule: AletheRule::AndPos(position),
                ..
            } => Some(*position),
            _ => None,
        })
        .collect();
    assert_eq!(
        positions.len(),
        1,
        "`(and p (and q r))` is FLATTENED, so the descent is one level"
    );
}

/// The MULTI-LEVEL descent, pinned directly on the emitter, because no
/// authored root can reach it (see above). The root here is built with the RAW
/// `mk_app`, which does not flatten, and the closed fragment is replayed by
/// the UNTOUCHED strict checker.
#[test]
fn a_two_level_descent_emits_one_and_pos_per_level_and_strict_checks() {
    let mut exec = solve(NESTED);
    let p = exec.ctx.terms.mk_var("p", Sort::Bool);
    let q = exec.ctx.terms.mk_var("q", Sort::Bool);
    let r = exec.ctx.terms.mk_var("r", Sort::Bool);
    let inner = exec
        .ctx
        .terms
        .mk_app(ay_core::Symbol::named("and"), vec![q, r], Sort::Bool);
    let root = exec
        .ctx
        .terms
        .mk_app(ay_core::Symbol::named("and"), vec![p, inner], Sort::Bool);
    let not_root = exec.ctx.terms.mk_not_raw(root);
    let not_inner = exec.ctx.terms.mk_not_raw(inner);
    let leaf = super::HypothesisLeaf::Conjunct {
        root,
        descents: vec![
            super::ConjunctDescent {
                position: 1,
                parent: root,
                not_parent: not_root,
                child: inner,
            },
            super::ConjunctDescent {
                position: 1,
                parent: inner,
                not_parent: not_inner,
                child: r,
            },
        ],
    };
    let mut fragment: Vec<ProofStep> = Vec::new();
    let mut root_assumes = ay_core::kani_compat::DetHashMap::default();
    let last = exec
        .push_hypothesis_leaf(&mut fragment, &mut root_assumes, &leaf, r)
        .expect("the two-level descent must emit");
    assert_eq!(last + 1, fragment.len());
    let positions: Vec<u32> = fragment
        .iter()
        .filter_map(|step| match step {
            ProofStep::Step {
                rule: AletheRule::AndPos(position),
                ..
            } => Some(*position),
            _ => None,
        })
        .collect();
    assert_eq!(positions, vec![1, 1], "one `and_pos` per nesting level");
    let closed = ay_proof::close_congruence_derivation(
        &mut exec.ctx.terms,
        &ay_proof::CongruenceDerivation {
            steps: fragment,
            clause: vec![r],
        },
    );
    ay_proof::check_proof_strict(&closed, &exec.ctx.terms)
        .expect("the two-level fragment must replay under the untouched strict checker");
}

#[test]
fn a_proof_carrying_an_anchor_is_left_alone() {
    let mut exec = solve(DISTINCT_STORECOMM);
    let atom = first_disequality(&mut exec);
    let mut proof = leaf_proof(&mut exec, atom, Vec::new(), Vec::new());
    proof.steps.push(ProofStep::Anchor {
        end_step: ProofId(0),
        variables: Vec::new(),
    });
    let before = shape(&proof);
    assert_eq!(rerun(&mut exec, &mut proof), 0);
    assert_eq!(shape(&proof), before, "an anchored proof must be untouched");
}

#[test]
fn a_trust_step_with_premises_is_left_alone() {
    let mut exec = solve(DISTINCT_STORECOMM);
    let atom = first_disequality(&mut exec);
    // A `trust` step WITH premises is a FAILED DERIVATION, not a leaf:
    // relabelling it would drop the premises its consumer references.
    let negated = exec.ctx.terms.mk_not(atom);
    let mut proof = ay_core::Proof::new();
    proof.steps.push(ProofStep::Assume(negated));
    proof.steps.push(ProofStep::Step {
        rule: AletheRule::Trust,
        clause: vec![atom],
        premises: vec![ProofId(0)],
        args: Vec::new(),
    });
    proof.steps.push(ProofStep::Step {
        rule: AletheRule::Resolution,
        clause: Vec::new(),
        premises: vec![ProofId(1), ProofId(0)],
        args: Vec::new(),
    });
    assert!(exec.check_proof_strict_with_datatypes(&proof).is_err());
    let before = shape(&proof);
    assert_eq!(rerun(&mut exec, &mut proof), 0);
    assert_eq!(
        shape(&proof),
        before,
        "a premise-bearing trust step must be untouched"
    );
}

#[test]
fn a_trust_step_with_args_is_left_alone() {
    let mut exec = solve(DISTINCT_STORECOMM);
    let atom = first_disequality(&mut exec);
    let mut proof = leaf_proof(&mut exec, atom, Vec::new(), vec![atom]);
    assert!(exec.check_proof_strict_with_datatypes(&proof).is_err());
    let before = shape(&proof);
    assert_eq!(rerun(&mut exec, &mut proof), 0);
    assert_eq!(
        shape(&proof),
        before,
        "an argument-bearing trust step must be untouched"
    );
}

#[test]
fn a_multi_literal_trust_step_is_left_alone() {
    let mut exec = solve(DISTINCT_STORECOMM);
    let atom = first_disequality(&mut exec);
    let other = last_disequality(&mut exec);
    let not_atom = exec.ctx.terms.mk_not(atom);
    let not_other = exec.ctx.terms.mk_not(other);
    let mut proof = ay_core::Proof::new();
    // A two-literal `trust` step is a CLAUSE, not a leaf: replacing it with a
    // unit derivation would drop a literal every consumer resolves against.
    proof.steps.push(ProofStep::Step {
        rule: AletheRule::Trust,
        clause: vec![atom, other],
        premises: Vec::new(),
        args: Vec::new(),
    });
    proof.steps.push(ProofStep::Assume(not_atom));
    proof.steps.push(ProofStep::Assume(not_other));
    proof.steps.push(ProofStep::Step {
        rule: AletheRule::Resolution,
        clause: vec![other],
        premises: vec![ProofId(0), ProofId(1)],
        args: Vec::new(),
    });
    proof.steps.push(ProofStep::Step {
        rule: AletheRule::Resolution,
        clause: Vec::new(),
        premises: vec![ProofId(3), ProofId(2)],
        args: Vec::new(),
    });
    assert!(exec.check_proof_strict_with_datatypes(&proof).is_err());
    let before = shape(&proof);
    assert_eq!(rerun(&mut exec, &mut proof), 0);
    assert_eq!(shape(&proof), before);
}

#[test]
fn the_root_itself_is_never_taken_as_its_own_conjunct() {
    let mut exec = solve(DISTINCT_STORECOMM);
    // The authored `and` root of the `distinct` expansion, taken from the
    // strict scope itself so the fixture cannot disagree with the solver.
    let root = exec
        .complete_problem_assertions_for_strict_proof()
        .into_iter()
        .find(|&term| {
            matches!(
                exec.ctx.terms.get(term),
                ay_core::TermData::App(ay_core::Symbol::Named(name), _) if name == "and"
            )
        })
        .expect("the distinct expansion is an authored `and`");
    let mut proof = leaf_proof(&mut exec, root, Vec::new(), Vec::new());
    assert_eq!(premiseless_unit_trust_leaves(&proof), 1);
    let before = shape(&proof);
    // The root IS an authored assertion; a `trust` step carrying it needs no
    // descent, and assuming it under the guise of a conjunct derivation would
    // be a one-step `assume` dressed up as a derivation.
    assert_eq!(rerun(&mut exec, &mut proof), 0);
    assert_eq!(shape(&proof), before);
}

#[test]
fn an_assertion_outside_the_handed_scope_is_never_assumed() {
    let mut exec = solve(DISTINCT_STORECOMM);
    let atom = first_disequality(&mut exec);
    let mut proof = leaf_proof(&mut exec, atom, Vec::new(), Vec::new());
    // The lane is handed a scope that does NOT contain the root it needs.
    let scope: Vec<TermId> = exec
        .complete_problem_assertions_for_strict_proof()
        .into_iter()
        .filter(|&term| {
            !matches!(
                exec.ctx.terms.get(term),
                ay_core::TermData::App(ay_core::Symbol::Named(name), _) if name == "and"
            )
        })
        .collect();
    let before = shape(&proof);
    assert_eq!(
        exec.derive_authored_conjunct_leaves(&mut proof, &scope),
        0,
        "the root is out of the handed scope, so nothing may be assumed"
    );
    assert_eq!(shape(&proof), before);
    // TWO-SIDED: with the root back in scope the SAME leaf is derived, so the
    // refusal is about MEMBERSHIP and not about the proof's shape.
    assert_eq!(rerun(&mut exec, &mut proof), 1);
}

#[test]
fn an_assertion_outside_the_strict_scope_is_never_assumed() {
    let mut exec = solve(NESTED);
    let r = exec.ctx.terms.mk_var("r", Sort::Bool);
    let p = exec.ctx.terms.mk_var("p", Sort::Bool);
    let q = exec.ctx.terms.mk_var("q", Sort::Bool);
    // A root that is NOT in the strict scope at all: a conjunction this
    // problem never authored. Handing it to the lane must change nothing,
    // because the intersection with the strict scope is empty.
    let _ = p;
    let forged = exec.ctx.terms.mk_and(vec![q, r]);
    assert!(
        !exec
            .complete_problem_assertions_for_strict_proof()
            .contains(&forged),
        "the forged root must genuinely be outside the strict scope"
    );
    let mut proof = leaf_proof(&mut exec, r, Vec::new(), Vec::new());
    let before = shape(&proof);
    assert_eq!(
        exec.derive_authored_conjunct_leaves(&mut proof, &[forged]),
        0,
        "a root outside the strict scope may not be assumed"
    );
    assert_eq!(shape(&proof), before);
    // TWO-SIDED: the SAME leaf IS derived from the authored root.
    assert_eq!(rerun(&mut exec, &mut proof), 1);
}
