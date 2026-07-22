// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! LIA-based Farkas interpolation.
//!
//! When no DPLL(T) Farkas history is available, this module runs a fresh LIA
//! solver on the conjunction of A∧B atoms, obtains a Farkas certificate, wraps
//! it in a one-step proof object, and delegates to `extract_interpolant_from_proof`
//! for Craig interpolant extraction.

use super::*;

pub(crate) fn compute_interpolant_from_lia_farkas(
    smt: &mut SmtContext,
    a_constraints: &[ChcExpr],
    b_constraints: &[ChcExpr],
    shared_vars: &FxHashSet<String>,
) -> Option<ChcExpr> {
    let a_flat = flatten_constraints(a_constraints);
    let b_flat = flatten_constraints(b_constraints);
    if a_flat.is_empty() || b_flat.is_empty() {
        return fail_lia_farkas_interpolant(
            &ZERO_FARKAS_LIA_FARKAS_PRECONDITION_FAILURES,
            "A or B partition is empty",
        );
    }
    if !a_flat.iter().all(is_linear_atom) || !b_flat.iter().all(is_linear_atom) {
        return fail_lia_farkas_interpolant(
            &ZERO_FARKAS_LIA_FARKAS_PRECONDITION_FAILURES,
            "A or B partition contains a non-linear atom",
        );
    }
    smt.reset_conversion_budget();

    let mut a_lits: FxHashSet<SignedLit> = FxHashSet::default();
    let mut b_lits: FxHashSet<SignedLit> = FxHashSet::default();
    let mut atom_to_expr: FxHashMap<TermId, ChcExpr> = FxHashMap::default();
    let mut atom_expr_to_term: FxHashMap<ChcExpr, TermId> = FxHashMap::default();

    let mut assertions: Vec<(TermId, bool)> = Vec::new();

    for c in a_flat.iter().chain(b_flat.iter()) {
        let (atom_expr, value) = match as_atom_and_value(c) {
            Some(av) => av,
            None => {
                return fail_lia_farkas_interpolant(
                    &ZERO_FARKAS_LIA_FARKAS_PRECONDITION_FAILURES,
                    "failed to normalize atom/polarity pair",
                );
            }
        };
        let atom_term = if let Some(&t) = atom_expr_to_term.get(&atom_expr) {
            t
        } else {
            let t = smt.convert_expr(&atom_expr);
            if smt.conversion_budget_exceeded() {
                return fail_lia_farkas_interpolant(
                    &ZERO_FARKAS_LIA_FARKAS_PRECONDITION_FAILURES,
                    "conversion budget exceeded while preparing LIA literals",
                );
            }
            atom_expr_to_term.insert(atom_expr.clone(), t);
            t
        };
        atom_to_expr.entry(atom_term).or_insert(atom_expr);
        assertions.push((atom_term, value));
    }

    for c in &a_flat {
        let (atom_expr, value) = match as_atom_and_value(c) {
            Some(av) => av,
            None => {
                return fail_lia_farkas_interpolant(
                    &ZERO_FARKAS_LIA_FARKAS_PRECONDITION_FAILURES,
                    "failed to normalize A-side atom",
                );
            }
        };
        let atom_term = match atom_expr_to_term.get(&atom_expr).copied() {
            Some(t) => t,
            None => {
                return fail_lia_farkas_interpolant(
                    &ZERO_FARKAS_LIA_FARKAS_PRECONDITION_FAILURES,
                    "A-side atom missing in conversion map",
                );
            }
        };
        a_lits.insert((atom_term, value));
    }
    for c in &b_flat {
        let (atom_expr, value) = match as_atom_and_value(c) {
            Some(av) => av,
            None => {
                return fail_lia_farkas_interpolant(
                    &ZERO_FARKAS_LIA_FARKAS_PRECONDITION_FAILURES,
                    "failed to normalize B-side atom",
                );
            }
        };
        let atom_term = match atom_expr_to_term.get(&atom_expr).copied() {
            Some(t) => t,
            None => {
                return fail_lia_farkas_interpolant(
                    &ZERO_FARKAS_LIA_FARKAS_PRECONDITION_FAILURES,
                    "B-side atom missing in conversion map",
                );
            }
        };
        b_lits.insert((atom_term, value));
    }

    let a_atoms: FxHashSet<TermId> = a_lits.iter().map(|(t, _)| *t).collect();
    let b_atoms: FxHashSet<TermId> = b_lits.iter().map(|(t, _)| *t).collect();

    // Run LIA directly on conjunction of atoms (no Boolean structure).
    let mut lia = LiaSolver::new(&smt.terms);
    for (t, v) in assertions {
        lia.assert_literal(t, v);
    }

    let TheoryResult::UnsatWithFarkas(conflict) = lia.check() else {
        return fail_lia_farkas_interpolant(
            &ZERO_FARKAS_LIA_FARKAS_NO_CERTIFICATE_FAILURES,
            "LIA check did not return Farkas conflict",
        );
    };
    let Some(farkas) = conflict.farkas.clone() else {
        return fail_lia_farkas_interpolant(
            &ZERO_FARKAS_LIA_FARKAS_NO_CERTIFICATE_FAILURES,
            "Farkas conflict has no coefficients",
        );
    };

    // Model the conflict as a single theory lemma with a Farkas annotation.
    // Clause literal i is the negation of conflict literal i (DPLL(T) blocking clause).
    let mut proof = Proof::new();
    let mut clause: Vec<TermId> = Vec::with_capacity(conflict.literals.len());
    for lit in &conflict.literals {
        let clause_lit = if lit.value {
            smt.terms.mk_not(lit.term)
        } else {
            lit.term
        };
        clause.push(clause_lit);
    }
    proof.add_step(ProofStep::TheoryLemma {
        theory: "LIA".to_string(),
        clause,
        farkas: Some(farkas),
        kind: TheoryLemmaKind::LiaGeneric,
        lia: None,
    });

    let Some(candidate) = extract_interpolant_from_proof(
        &proof,
        &smt.terms,
        &a_lits,
        &a_atoms,
        &b_atoms,
        &atom_to_expr,
        shared_vars,
    ) else {
        return fail_lia_farkas_interpolant(
            &ZERO_FARKAS_LIA_FARKAS_PROOF_EXTRACTION_FAILURES,
            "extract_interpolant_from_proof returned None",
        );
    };

    iuc_trace!(
        "compute_interpolant_from_lia_farkas: candidate = {}",
        candidate
    );

    // Verify Craig properties using shared helper
    let a_conj = ChcExpr::and_all(a_flat);
    let b_conj = ChcExpr::and_all(b_flat);

    if verify_craig_properties(
        &candidate,
        &a_conj,
        &b_conj,
        shared_vars,
        smt,
        "compute_interpolant_from_lia_farkas",
    ) {
        Some(candidate)
    } else {
        fail_lia_farkas_interpolant(
            &ZERO_FARKAS_LIA_FARKAS_CRAIG_FAILURES,
            "candidate failed Craig property validation",
        )
    }
}
