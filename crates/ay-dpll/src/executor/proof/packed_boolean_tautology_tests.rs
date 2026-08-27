// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Coverage for the packed Boolean-tautology lane.
//!
//! **Every fixture is a COMPLETE refutation** — a proof whose last clause is
//! the EMPTY clause, with every `assume` it needs present. That is deliberate
//! and it is the sibling passes' hard-won lesson: on a truncated fixture a
//! guard mutation comes back green because some backstop reverted the rewrite
//! for a reason that has nothing to do with the guard. Here the lane's own
//! commit gate (`commit_bridge_fragments`) re-checks the WHOLE proof, so a
//! fixture that is not a real refutation would revert unconditionally and
//! every mutation would look safe.
//!
//! The independent oracle for this class is a TRUTH TABLE. The lane's own
//! authority is `ay_proof::check_proof_strict`; `eval_boolean` below shares no
//! code with it or with the emitter — it is a self-contained recursive
//! evaluator over `TermData` — so an accept re-checked by it is checked twice
//! by two unrelated implementations.

use super::super::*;

use ay_core::kani_compat::DetHashMap;
use ay_core::{Constant, Sort, Symbol, TermData, TermId, TermStore};

// ===== the independent oracle =====

/// Evaluate `term` under `assignment`, treating any term that is not `not`,
/// `and`, `or` or a Boolean `=` as an opaque atom.
///
/// This shares NO code with the emitter or with `ay-proof`'s checker: it is a
/// direct recursive reading of the term DAG. `None` means the term mentions an
/// atom the assignment does not bind, which every caller treats as a failure.
pub(super) fn eval_boolean(
    terms: &TermStore,
    assignment: &DetHashMap<TermId, bool>,
    term: TermId,
) -> Option<bool> {
    if let Some(&value) = assignment.get(&term) {
        return Some(value);
    }
    match terms.get(term) {
        TermData::Not(inner) => Some(!eval_boolean(terms, assignment, *inner)?),
        TermData::Const(Constant::Bool(value)) => Some(*value),
        TermData::App(Symbol::Named(name), args) => {
            let name = name.clone();
            let args = args.clone();
            match name.as_str() {
                "not" => {
                    let [inner] = args.as_slice() else {
                        return None;
                    };
                    Some(!eval_boolean(terms, assignment, *inner)?)
                }
                "and" => {
                    let mut value = true;
                    for arg in args {
                        value &= eval_boolean(terms, assignment, arg)?;
                    }
                    Some(value)
                }
                "or" => {
                    let mut value = false;
                    for arg in args {
                        value |= eval_boolean(terms, assignment, arg)?;
                    }
                    Some(value)
                }
                "=" => {
                    let [lhs, rhs] = args.as_slice() else {
                        return None;
                    };
                    // Only a BOOLEAN equality is an equivalence; anything else
                    // must have been bound as an atom.
                    if !matches!(terms.sort(*lhs), Sort::Bool) {
                        return None;
                    }
                    Some(
                        eval_boolean(terms, assignment, *lhs)?
                            == eval_boolean(terms, assignment, *rhs)?,
                    )
                }
                _ => None,
            }
        }
        _ => None,
    }
}

/// Whether the clause `literals` is TRUE under every assignment to `atoms` —
/// decided by exhaustive enumeration, not by any schema.
pub(super) fn is_tautology(terms: &TermStore, atoms: &[TermId], literals: &[TermId]) -> bool {
    falsifying_assignment(terms, atoms, literals).is_none()
}

/// A concrete assignment falsifying every literal of `literals`, or `None`.
pub(super) fn falsifying_assignment(
    terms: &TermStore,
    atoms: &[TermId],
    literals: &[TermId],
) -> Option<Vec<(TermId, bool)>> {
    assert!(atoms.len() < 16, "the sweep alphabet must stay bounded");
    for bits in 0u32..(1u32 << atoms.len()) {
        let mut assignment: DetHashMap<TermId, bool> = DetHashMap::default();
        let mut named = Vec::new();
        for (index, &atom) in atoms.iter().enumerate() {
            let value = bits & (1 << index) != 0;
            assignment.insert(atom, value);
            named.push((atom, value));
        }
        let mut satisfied = false;
        for &literal in literals {
            let value = eval_boolean(terms, &assignment, literal)
                .expect("the oracle must bind every atom of the fixture");
            satisfied |= value;
        }
        if !satisfied {
            return Some(named);
        }
    }
    None
}

// ===== fixtures =====

/// The two Boolean atoms of the MEASURED head, and the equality between them.
///
/// Measured on `benchmarks/smt/chc_multi_pred_array.smt2`: `X` is a Boolean
/// array READ and `Y` is an index equality, and the leaf is their equivalence
/// packed into one `or`. The array content is incidental — what matters is
/// that both are Boolean-sorted opaque atoms.
pub(super) struct Atoms {
    pub(super) x: TermId,
    pub(super) y: TermId,
    pub(super) z: TermId,
    pub(super) eq_xy: TermId,
}

pub(super) fn atoms(executor: &mut Executor) -> Atoms {
    let index_sort = Sort::bitvec(32);
    let array_sort = Sort::Array(Box::new(ay_core::ArraySort::new(
        index_sort.clone(),
        Sort::Bool,
    )));
    let array = executor.ctx.terms.mk_var("allocate_0_0", array_sort);
    let witness = executor
        .ctx
        .terms
        .mk_var("ay_ext_diff_21", index_sort.clone());
    let constant = executor.ctx.terms.mk_var("zero_32", index_sort);
    let x = executor
        .ctx
        .terms
        .mk_app(Symbol::named("select"), vec![array, witness], Sort::Bool);
    let y = executor
        .ctx
        .terms
        .mk_app(Symbol::named("="), vec![constant, witness], Sort::Bool);
    let z = executor.ctx.terms.mk_var("unrelated_bool", Sort::Bool);
    let eq_xy = executor
        .ctx
        .terms
        .mk_app(Symbol::named("="), vec![x, y], Sort::Bool);
    Atoms { x, y, z, eq_xy }
}

pub(super) fn or_term(executor: &mut Executor, literals: Vec<TermId>) -> TermId {
    executor
        .ctx
        .terms
        .mk_app(Symbol::named("or"), literals, Sort::Bool)
}

pub(super) fn trust_leaf(clause: Vec<TermId>) -> ProofStep {
    ProofStep::Step {
        rule: AletheRule::Trust,
        clause,
        premises: Vec::new(),
        args: Vec::new(),
    }
}

/// A COMPLETE refutation whose only uncertified step is the packed leaf.
///
/// The proof assumes the complement of each disjunct, resolves them against
/// the packed unit's `or` unpacking, and ends on the EMPTY clause. Every
/// `assume` is a problem assertion of the fixture, so `commit_bridge_fragments`
/// has a real proof to re-check rather than a fragment that reverts anyway.
pub(super) fn complete_refutation(
    executor: &mut Executor,
    literals: &[TermId],
) -> (Proof, TermId, Vec<TermId>) {
    let packed = or_term(executor, literals.to_vec());
    let mut proof = Proof::new();
    let leaf = proof.add_step(trust_leaf(vec![packed]));
    let mut current = proof.add_step(ProofStep::Step {
        rule: AletheRule::Or,
        clause: literals.to_vec(),
        premises: vec![leaf],
        args: Vec::new(),
    });
    let mut remaining = literals.to_vec();
    let mut assumptions = Vec::new();
    for &literal in literals {
        let negated = executor.ctx.terms.mk_not(literal);
        assumptions.push(negated);
        let assumed = proof.add_step(ProofStep::Assume(negated));
        remaining.retain(|&other| other != literal);
        current = proof.add_step(ProofStep::Step {
            rule: AletheRule::Resolution,
            clause: remaining.clone(),
            premises: vec![current, assumed],
            args: Vec::new(),
        });
    }
    assert!(
        matches!(
            proof.steps.last(),
            Some(ProofStep::Step { clause, .. }) if clause.is_empty()
        ),
        "the fixture must be a COMPLETE refutation, ending on the empty clause"
    );
    let _ = current;
    // The fixture's assumptions ARE its problem, so the strict gate sees the
    // same authored window a real solve would hand it. Without this the
    // refutation is complete but every `assume` is unauthorized, and the
    // whole-proof commit gate would revert for a reason unrelated to any guard.
    executor.set_self_check_authored_assertions_for_tests(assumptions.clone());
    (proof, packed, assumptions)
}

/// Run the lane over a complete refutation and report how many leaves it
/// replaced.
pub(super) fn run_lane(executor: &mut Executor, proof: &mut Proof) -> usize {
    executor.derive_packed_boolean_tautologies(proof)
}

pub(super) fn rules_of(proof: &Proof) -> Vec<String> {
    proof
        .steps
        .iter()
        .filter_map(|step| match step {
            ProofStep::Step { rule, .. } => Some(rule.name().to_string()),
            _ => None,
        })
        .collect()
}

// ===== 1. the measured head closes =====

/// The MEASURED leaf — `(cl (or (= X Y) (not X) (not Y)))` — is derived, and
/// the derivation ends on that same packed unit byte for byte.
#[test]
fn the_measured_packed_equivalence_leaf_is_derived() {
    let mut executor = Executor::new();
    let a = atoms(&mut executor);
    let not_x = executor.ctx.terms.mk_not(a.x);
    let not_y = executor.ctx.terms.mk_not(a.y);
    let literals = vec![a.eq_xy, not_x, not_y];
    // PRECONDITION, checked by the INDEPENDENT oracle: the fixture really is
    // a tautology. Without this the test could pass for the wrong reason.
    assert!(
        is_tautology(&executor.ctx.terms, &[a.x, a.y], &literals),
        "the measured head must be a propositional tautology"
    );
    let (mut proof, packed, _) = complete_refutation(&mut executor, &literals);
    assert_eq!(run_lane(&mut executor, &mut proof), 1);

    assert!(
        !proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::Step {
                rule: AletheRule::Trust,
                ..
            }
        )),
        "no trust step may survive: {:?}",
        rules_of(&proof)
    );
    let rules = rules_of(&proof);
    assert!(
        rules.iter().any(|rule| rule == "equiv_neg1"),
        "the flat clause is an equiv_neg1: {rules:?}"
    );
    assert!(
        rules.iter().filter(|rule| *rule == "or_neg").count() == literals.len(),
        "one or_neg per disjunct: {rules:?}"
    );
    // The spliced fragment must still END on the leaf's own clause, so no
    // consumer had to be touched.
    assert!(
        proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::Step { rule: AletheRule::ThResolution, clause, .. }
                if clause.as_slice() == [packed]
        )),
        "the fragment must end on the packed unit"
    );
    executor
        .check_proof_strict_with_datatypes(&proof)
        .expect("the rebuilt proof must strict-check");
}

/// All four equivalence orientations the corpus carries are closed — measured
/// as 32 `equiv_neg1`, 32 `equiv_neg2`, 24 `equiv_pos1`, 22 `equiv_pos2`.
#[test]
fn every_measured_equivalence_orientation_is_closed() {
    for orientation in 0..4u8 {
        let mut executor = Executor::new();
        let a = atoms(&mut executor);
        let not_x = executor.ctx.terms.mk_not(a.x);
        let not_y = executor.ctx.terms.mk_not(a.y);
        let not_eq = executor.ctx.terms.mk_not(a.eq_xy);
        let literals = match orientation {
            0 => vec![a.eq_xy, not_x, not_y],
            1 => vec![a.eq_xy, a.x, a.y],
            2 => vec![not_eq, a.x, not_y],
            _ => vec![not_eq, not_x, a.y],
        };
        assert!(
            is_tautology(&executor.ctx.terms, &[a.x, a.y], &literals),
            "orientation {orientation} must be a tautology"
        );
        let (mut proof, _, _) = complete_refutation(&mut executor, &literals);
        assert_eq!(
            run_lane(&mut executor, &mut proof),
            1,
            "orientation {orientation} must be derived"
        );
        executor
            .check_proof_strict_with_datatypes(&proof)
            .unwrap_or_else(|error| panic!("orientation {orientation} must strict-check: {error}"));
    }
}

// ===== 2. exhaustive sweep, every ACCEPT re-checked independently =====

/// EXHAUSTIVE sweep over every three-literal clause built from the polarities
/// of `X`, `Y` and `(= X Y)`, with every ACCEPT re-checked by the INDEPENDENT
/// truth-table oracle.
///
/// This is the property that matters: the lane may accept only clauses that
/// are genuinely valid. The sweep also records that the lane is not vacuous —
/// it must accept at least the four measured orientations.
#[test]
fn every_accept_in_the_exhaustive_sweep_is_a_tautology_by_the_independent_oracle() {
    let mut executor = Executor::new();
    let a = atoms(&mut executor);
    let not_x = executor.ctx.terms.mk_not(a.x);
    let not_y = executor.ctx.terms.mk_not(a.y);
    let not_z = executor.ctx.terms.mk_not(a.z);
    let not_eq = executor.ctx.terms.mk_not(a.eq_xy);
    let alphabet = [a.eq_xy, not_eq, a.x, not_x, a.y, not_y, a.z, not_z];
    let sweep_atoms = [a.x, a.y, a.z];

    let mut accepted = 0usize;
    let mut rejected = 0usize;
    for &first in &alphabet {
        for &second in &alphabet {
            for &third in &alphabet {
                let literals = vec![first, second, third];
                let rule = executor.strict_checked_tautology_rule(&literals);
                let Some(rule) = rule else {
                    rejected += 1;
                    continue;
                };
                accepted += 1;
                // The INDEPENDENT oracle decides, with a NAMED counterexample
                // in the failure message when it disagrees.
                if let Some(witness) =
                    falsifying_assignment(&executor.ctx.terms, &sweep_atoms, &literals)
                {
                    panic!(
                        "the checker accepted {} for a clause the truth table FALSIFIES at {:?}",
                        rule.name(),
                        witness
                    );
                }
            }
        }
    }
    assert_eq!(
        accepted + rejected,
        alphabet.len().pow(3),
        "the sweep must be exhaustive"
    );
    assert!(
        accepted >= 4,
        "the sweep must not be vacuous: it accepted {accepted} of {}",
        alphabet.len().pow(3)
    );
}
