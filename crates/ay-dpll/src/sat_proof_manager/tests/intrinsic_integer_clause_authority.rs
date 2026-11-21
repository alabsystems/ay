// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::{Proof, ProofStep, TheoryLemmaKind};

fn app(terms: &mut TermStore, operator: &str, args: &[TermId], sort: Sort) -> TermId {
    terms.mk_app(Symbol::named(operator), args, sort)
}

/// The actual captured parity cut, with the original x and two UF reads.
fn parity_atoms(terms: &mut TermStore, upper: i64) -> ([TermId; 3], [TermId; 3]) {
    let x = terms.mk_var("x", Sort::Int);
    let zero = terms.mk_int(0.into());
    let one = terms.mk_int(1.into());
    let two = terms.mk_int(2.into());
    let three = terms.mk_int(3.into());
    let minus_two = terms.mk_int((-2).into());
    let upper = terms.mk_int(upper.into());
    let x2 = app(terms, "+", &[x, two], Sort::Int);
    let q0 = app(terms, "q", &[x, two], Sort::Int);
    let q2 = app(terms, "q", &[x2, two], Sort::Int);
    let nq0 = app(terms, "*", &[q0, minus_two], Sort::Int);
    let nq2 = app(terms, "*", &[q2, minus_two], Sort::Int);
    let r0 = app(terms, "+", &[x, nq0], Sort::Int);
    let r2 = app(terms, "+", &[x, nq2, two], Sort::Int);
    let nonpositive = app(terms, "<=", &[r2, zero], Sort::Bool);
    let zero0 = app(terms, "=", &[zero, r0], Sort::Bool);
    let bounded = app(terms, "<=", &[r2, upper], Sort::Bool);
    let zero2 = app(terms, "=", &[zero, r2], Sort::Bool);
    let rm1 = app(terms, "+", &[x, nq2, one], Sort::Int);
    let rp1 = app(terms, "+", &[x, nq2, three], Sort::Int);
    let ge = app(terms, "<=", &[zero, rm1], Sort::Bool);
    let le = app(terms, "<=", &[rp1, zero], Sort::Bool);
    ([nonpositive, zero0, bounded], [zero2, ge, le])
}

fn fragment(
    terms: &mut TermStore,
    atoms: &[TermId],
    clause: Vec<Literal>,
) -> Result<ExactOriginalProofFragment, ExactOriginalProofError> {
    let map: HashMap<_, _> = atoms
        .iter()
        .copied()
        .enumerate()
        .map(|(i, term)| (u32::try_from(i).unwrap(), term))
        .collect();
    let mut trace = ClauseTrace::new();
    trace.add_clause(130, clause, true);
    SatProofManager::new(&map, terms).build_exact_original_proof_fragment(&trace, &[])
}

#[test]
fn intrinsic_integer_clause_parity_cut_strictly_certifies_without_an_assumption() {
    let mut terms = TermStore::new();
    let (atoms, _) = parity_atoms(&mut terms, 1);
    let [nonpositive, even, bounded] = atoms;
    let fragment = fragment(
        &mut terms,
        &atoms,
        vec![
            Literal::positive(Variable::new(0)),
            Literal::negative(Variable::new(2)),
            Literal::negative(Variable::new(1)),
        ],
    )
    .expect("integer cut replay is independent of a SAT inference record");
    let cut = fragment.bindings[&130].proof_id;
    let mut proof = fragment.proof;
    let not_even = terms.mk_not_raw(even);
    let not_bounded = terms.mk_not_raw(bounded);
    assert!(matches!(proof.get_step(cut), Some(ProofStep::TheoryLemma {
        kind: TheoryLemmaKind::IntCgCutChain, clause, ..
    }) if clause.as_slice() == [nonpositive, not_bounded, not_even]));
    let positive = terms.mk_not_raw(nonpositive);
    let first = proof.add_assume(positive, None);
    let second = proof.add_assume(even, None);
    let third = proof.add_assume(bounded, None);
    let tail = proof.add_resolution(vec![not_even, not_bounded], nonpositive, cut, first);
    let tail = proof.add_resolution(vec![not_bounded], even, tail, second);
    proof.add_resolution(Vec::new(), bounded, tail, third);
    check_strict_wire(&terms, &proof, &[positive, even, bounded]);
}

#[test]
fn intrinsic_integer_clause_declines_the_looser_satisfiable_twin() {
    let mut terms = TermStore::new();
    let (atoms, _) = parity_atoms(&mut terms, 2);
    let result = fragment(
        &mut terms,
        &atoms,
        vec![
            Literal::positive(Variable::new(0)),
            Literal::negative(Variable::new(1)),
            Literal::negative(Variable::new(2)),
        ],
    );
    assert!(matches!(
        result,
        Err(ExactOriginalProofError::UnauthenticatedOriginalClause { clause_id: 130, .. })
    ));
}

#[test]
fn intrinsic_integer_clause_reconstructs_the_packed_trichotomy() {
    let mut terms = TermStore::new();
    let (_, disjuncts) = parity_atoms(&mut terms, 1);
    let packed = app(&mut terms, "or", &disjuncts, Sort::Bool);
    let fragment = fragment(
        &mut terms,
        &[packed],
        vec![Literal::positive(Variable::new(0))],
    )
    .expect("the split and both integer strengthening legs are checked");
    let step = fragment.bindings[&130].proof_id;
    let mut proof = fragment.proof;
    assert!(
        matches!(proof.get_step(step), Some(ProofStep::Step { clause, .. })
        if clause.as_slice() == [packed])
    );
    let negated = terms.mk_not_raw(packed);
    let assume = proof.add_assume(negated, None);
    proof.add_resolution(Vec::new(), packed, step, assume);
    check_strict_wire(&terms, &proof, &[negated]);
}

#[test]
fn intrinsic_integer_clause_refuses_a_trichotomy_with_a_missing_integer() {
    let mut terms = TermStore::new();
    let (atoms, [equal, _, lower]) = parity_atoms(&mut terms, 2);
    let TermData::App(_, upper_args) = terms.get(atoms[2]) else {
        unreachable!();
    };
    let [value, two] = upper_args.as_slice() else {
        unreachable!();
    };
    let (value, two) = (*value, *two);
    let upper = app(&mut terms, "<=", &[two, value], Sort::Bool);
    let packed = app(&mut terms, "or", &[equal, upper, lower], Sort::Bool);
    let result = fragment(
        &mut terms,
        &[packed],
        vec![Literal::positive(Variable::new(0))],
    );
    assert!(matches!(
        result,
        Err(ExactOriginalProofError::UnauthenticatedOriginalClause { clause_id: 130, .. })
    ));
}

#[test]
fn intrinsic_integer_clause_requires_typed_input_and_live_budget() {
    use crate::theory_inference::intrinsic_integer::IntrinsicIntegerClause;

    let mut terms = TermStore::new();
    let (atoms, _) = parity_atoms(&mut terms, 1);
    let clause = [
        atoms[0],
        terms.mk_not_raw(atoms[1]),
        terms.mk_not_raw(atoms[2]),
    ];
    let mut admitted = Vec::new();
    assert!(
        IntrinsicIntegerClause::admit(&terms, &clause, &mut |work, bytes| {
            admitted.push((work, bytes));
            false
        })
        .is_none()
    );
    assert!(matches!(admitted.as_slice(), [(work, bytes)] if *work > 0 && *bytes > 0));
    let plan = IntrinsicIntegerClause::admit(&terms, &clause, &mut |_, _| true).unwrap();
    let mut proof = Proof::new();
    assert!(plan
        .emit(&mut terms, &mut proof, &mut |_, _| false)
        .is_none());
    assert!(proof.steps.is_empty());
    let real = terms.mk_var("non_integer", Sort::Real);
    let real_bound = app(&mut terms, "<=", &[real, real], Sort::Bool);
    assert!(IntrinsicIntegerClause::admit(
        &terms,
        &[real_bound, clause[1], clause[2]],
        &mut |_, _| true
    )
    .is_none());
    assert!(IntrinsicIntegerClause::admit(
        &terms,
        &[TermId(u32::MAX), clause[1], clause[2]],
        &mut |_, _| true
    )
    .is_none());
}

#[test]
fn intrinsic_integer_clause_replays_captured_two_literal_rounding_covers() {
    for shape in 0..2 {
        let mut terms = TermStore::new();
        let x = terms.mk_var("cover_x", Sort::Int);
        let two = terms.mk_int(2.into());
        let one = terms.mk_int(1.into());
        let zero = terms.mk_int(0.into());
        let minus_one = terms.mk_int((-1).into());
        let minus_two = terms.mk_int((-2).into());
        let x2 = app(&mut terms, "+", &[x, two], Sort::Int);
        let q0 = app(&mut terms, "cover_q", &[x, two], Sort::Int);
        let q2 = app(&mut terms, "cover_q", &[x2, two], Sort::Int);
        let n0 = app(&mut terms, "*", &[q0, minus_two], Sort::Int);
        let n2 = app(&mut terms, "*", &[q2, minus_two], Sort::Int);
        let r0 = app(&mut terms, "+", &[x, n0], Sort::Int);
        let r2 = app(&mut terms, "+", &[x, n2], Sort::Int);
        let q0_plus_one = app(&mut terms, "+", &[q0, one], Sort::Int);
        let clause = if shape == 0 {
            // Exact shape of original clause7123: the UF reads are opaque
            // Int atoms. Only integer discreteness licenses this cover.
            vec![
                app(&mut terms, "<=", &[r0, r2], Sort::Bool),
                app(&mut terms, "<=", &[q0_plus_one, q2], Sort::Bool),
            ]
        } else {
            // Exact bound-only shape of original clause16658.
            let shifted = app(&mut terms, "+", &[n0, minus_one], Sort::Int);
            let bound = app(&mut terms, "<=", &[zero, shifted], Sort::Bool);
            vec![
                terms.mk_not_raw(bound),
                app(&mut terms, "<=", &[q0_plus_one, zero], Sort::Bool),
            ]
        };
        strict_tautology_fragment(&mut terms, &clause);
        let mut loose = clause.clone();
        let three = terms.mk_int(3.into());
        let shifted = app(&mut terms, "+", &[q0, three], Sort::Int);
        loose[1] = app(
            &mut terms,
            "<=",
            &[shifted, if shape == 0 { q2 } else { zero }],
            Sort::Bool,
        );
        let result = fragment(
            &mut terms,
            &loose,
            vec![
                Literal::positive(Variable::new(0)),
                Literal::positive(Variable::new(1)),
            ],
        );
        assert!(matches!(
            result,
            Err(ExactOriginalProofError::UnauthenticatedOriginalClause { .. })
        ));
    }
}

#[test]
fn intrinsic_integer_clause_replays_captured_three_bound_linear_conflict() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("bounds_x", Sort::Int);
    let q0 = terms.mk_var("bounds_q0", Sort::Int);
    let q2 = terms.mk_var("bounds_q2", Sort::Int);
    let two = terms.mk_int(2.into());
    let minus_two = terms.mk_int((-2).into());
    let minus_one = terms.mk_int((-1).into());
    let n0 = app(&mut terms, "*", &[q0, minus_two], Sort::Int);
    let n2 = app(&mut terms, "*", &[q2, minus_two], Sort::Int);
    let r0 = app(&mut terms, "+", &[x, n0], Sort::Int);
    let r2 = app(&mut terms, "+", &[x, n2], Sort::Int);
    let shifted = app(&mut terms, "+", &[x, two], Sort::Int);
    let shifted = app(&mut terms, "+", &[shifted, n2], Sort::Int);
    let le = app(&mut terms, "<=", &[r0, r2], Sort::Bool);
    let upper = app(&mut terms, "<", &[shifted, two], Sort::Bool);
    let clause = [
        terms.mk_not_raw(le),
        terms.mk_not_raw(upper),
        app(&mut terms, "<=", &[r0, minus_one], Sort::Bool),
    ];
    strict_tautology_fragment(&mut terms, &clause);
    // Losing strictness permits r0=r2=0. Neither the integer strengthening
    // nor a cut may turn this changed, satisfiable clause into a theorem.
    let loose_upper = app(&mut terms, "<=", &[shifted, two], Sort::Bool);
    let loose = [clause[0], terms.mk_not_raw(loose_upper), clause[2]];
    let result = fragment(
        &mut terms,
        &loose,
        vec![
            Literal::positive(Variable::new(0)),
            Literal::positive(Variable::new(1)),
            Literal::positive(Variable::new(2)),
        ],
    );
    assert!(matches!(
        result,
        Err(ExactOriginalProofError::UnauthenticatedOriginalClause { .. })
    ));
}

struct ClauseBudget {
    work: usize,
    storage: usize,
    refused: bool,
    cut_charges: usize,
}

impl ClauseBudget {
    fn pay(&mut self, work: usize, storage: usize) -> bool {
        if self.refused {
            return false;
        }
        // The existing bounded cut search fee, unchanged by the branch move.
        if (work, storage) == (65_536, 262_144) {
            self.cut_charges += 1;
        }
        let (Some(remaining_work), Some(remaining_storage)) = (
            self.work.checked_sub(work),
            self.storage.checked_sub(storage),
        ) else {
            self.refused = true;
            return false;
        };
        self.work = remaining_work;
        self.storage = remaining_storage;
        true
    }
}

fn budget_bounds(terms: &mut TermStore, scaled: bool) -> [TermId; 2] {
    let x = terms.mk_var("budget_x", Sort::Int);
    let y = terms.mk_var("budget_y", Sort::Int);
    let one = terms.mk_int(1.into());
    let next_y = app(terms, "+", &[y, one], Sort::Int);
    let (left, right) = if scaled {
        let two = terms.mk_int(2.into());
        (
            app(terms, "*", &[two, x], Sort::Int),
            app(terms, "*", &[two, y], Sort::Int),
        )
    } else {
        (x, y)
    };
    [
        app(terms, "<=", &[left, right], Sort::Bool),
        app(terms, "<=", &[next_y, x], Sort::Bool),
    ]
}

fn close_budgeted_clause(
    terms: &mut TermStore,
    mut proof: Proof,
    mut tail: ay_core::ProofId,
    clause: &[TermId],
) {
    let mut roots = Vec::new();
    for (position, &literal) in clause.iter().enumerate() {
        let negated = terms.mk_not_raw(literal);
        roots.push(negated);
        let assumption = proof.add_assume(negated, None);
        tail = proof.add_resolution(clause[position + 1..].to_vec(), literal, tail, assumption);
    }
    check_strict_wire(terms, &proof, &roots);
}

#[test]
fn intrinsic_integer_clause_unit_farkas_does_not_spend_an_unused_cut_allowance() {
    use crate::theory_inference::intrinsic_integer::IntrinsicIntegerClause;

    let mut terms = TermStore::new();
    let clause = budget_bounds(&mut terms, false);
    let mut budget = ClauseBudget {
        // This original allowance is below even ONE fixed cut-search offer.
        // The actual independently metered Farkas derivation still fits it.
        work: 65_535,
        storage: 262_143,
        refused: false,
        cut_charges: 0,
    };
    let plan = IntrinsicIntegerClause::admit(&terms, &clause, &mut |w, b| budget.pay(w, b))
        .expect("the physical clause fits the same original allowance");
    let mut proof = Proof::new();
    let id = plan
        .emit(&mut terms, &mut proof, &mut |w, b| budget.pay(w, b))
        .expect("unit Farkas needs no unexecuted cut search");
    assert!(!budget.refused);
    assert_eq!(budget.cut_charges, 0);
    assert_eq!(proof.steps.len(), 1);
    assert!(matches!(proof.get_step(id), Some(ProofStep::TheoryLemma {
        kind: TheoryLemmaKind::LraFarkas, clause: derived, farkas: Some(_), ..
    }) if derived.as_slice() == clause));
    close_budgeted_clause(&mut terms, proof, id, &clause);
}

#[test]
fn intrinsic_integer_clause_real_cut_prepays_its_full_allowance() {
    use crate::theory_inference::intrinsic_integer::IntrinsicIntegerClause;

    let mut terms = TermStore::new();
    let clause = budget_bounds(&mut terms, true);
    let mut budget = ClauseBudget {
        work: 1_048_576,
        storage: 8_388_608,
        refused: false,
        cut_charges: 0,
    };
    let plan =
        IntrinsicIntegerClause::admit(&terms, &clause, &mut |w, b| budget.pay(w, b)).unwrap();
    let mut proof = Proof::new();
    let id = plan
        .emit(&mut terms, &mut proof, &mut |w, b| budget.pay(w, b))
        .unwrap();
    assert_eq!(budget.cut_charges, 1);
    assert!(!budget.refused);
    assert!(matches!(proof.get_step(id), Some(ProofStep::TheoryLemma {
        kind: TheoryLemmaKind::IntCgCutChain, clause: derived, farkas: None, ..
    }) if derived.as_slice() == clause));
    close_budgeted_clause(&mut terms, proof, id, &clause);
}

#[test]
fn intrinsic_integer_clause_real_cut_cannot_run_after_its_fee_refuses() {
    use crate::theory_inference::intrinsic_integer::IntrinsicIntegerClause;

    let mut terms = TermStore::new();
    let clause = budget_bounds(&mut terms, true);
    let mut budget = ClauseBudget {
        work: 65_535,
        storage: 262_143,
        refused: false,
        cut_charges: 0,
    };
    let plan =
        IntrinsicIntegerClause::admit(&terms, &clause, &mut |w, b| budget.pay(w, b)).unwrap();
    let old_terms = terms.len();
    let mut proof = Proof::new();
    assert!(plan
        .emit(&mut terms, &mut proof, &mut |w, b| budget.pay(w, b))
        .is_none());
    assert!(budget.refused);
    assert_eq!(budget.cut_charges, 1);
    assert_eq!(terms.len(), old_terms);
    assert!(proof.steps.is_empty());
    let remaining = (budget.work, budget.storage);
    assert!(plan
        .emit(&mut terms, &mut proof, &mut |w, b| budget.pay(w, b))
        .is_none());
    assert_eq!((budget.work, budget.storage), remaining);
    assert_eq!(
        budget.cut_charges, 1,
        "a stopped owner never reaches another cut search"
    );
    assert!(proof.steps.is_empty());
}

fn strict_tautology_fragment(terms: &mut TermStore, clause: &[TermId]) {
    let literals: Vec<_> = (0..clause.len())
        .map(|i| Literal::positive(Variable::new(u32::try_from(i).unwrap())))
        .collect();
    let result =
        fragment(terms, clause, literals).expect("exact integer clause has checked authority");
    let mut proof = result.proof;
    let mut tail = result.bindings[&130].proof_id;
    let mut residual = clause.to_vec();
    let mut roots = Vec::new();
    for &literal in clause {
        let negated = match terms.get(literal) {
            TermData::Not(inner) => *inner,
            _ => terms.mk_not_raw(literal),
        };
        roots.push(negated);
        let unit = proof.add_assume(negated, None);
        residual.remove(0);
        tail = proof.add_resolution(residual.clone(), literal, tail, unit);
    }
    check_strict_wire(terms, &proof, &roots);
}

fn check_strict_wire(terms: &TermStore, proof: &Proof, assumptions: &[TermId]) {
    ay_proof::validate_reachable_assumes_in_problem_scope(proof, assumptions)
        .expect("only the exact authored premises are present");
    let quality = ay_proof::check_proof_strict(proof, terms).expect("strict integer proof");
    assert!(quality.is_complete(), "{quality:?}");
    let wire = ay_proof::try_export_alethe_with_problem_scope_and_overrides(
        proof,
        terms,
        assumptions,
        None,
    )
    .expect("paired Alethe proof");
    assert!(wire.contains(":rule la_generic"), "{wire}");
    assert!(!wire.contains(":rule hole"), "{wire}");
    assert!(!wire.contains(":rule trust"), "{wire}");
}
