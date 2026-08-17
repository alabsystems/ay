// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

/// Apply a scoped theory lemma clause to the incremental SAT solver.
///
/// Used by the lazy incremental split-loop to keep theory lemmas SAT-visible
/// across split iterations without rebuilding from scratch. Lemmas go on the
/// scoped ORIGINAL ledger (`add_clause`), NOT the learned tier: a learned
/// clause is silently discarded by `reset_search_state`'s destructive arena
/// rebuild mid-loop while the persistent `TheoryLemmaSeenSet` (and the
/// theory-side `note_applied_theory_lemma` replay) suppress re-adding — the
/// SAT model then revisits the excluded assignment forever, or the eager
/// pipeline's "all lemma atoms already encoded" fallthrough ACCEPTS a model
/// the wiped lemma excludes (#lemma-wipe class, extends 4d4a297b). The
/// ledger survives every rebuild for the life of the scope, restoring the
/// invariant every dedup here assumes: added once ⇒ present until pop.
// #8529: Use deterministic hash sets in all builds.
use ay_core::kani_compat::DetHashSet as HashSet;

/// Keep only theory lemmas that have not already been made SAT-visible.
///
/// This is intentionally a pure replay guard: it does not weaken, merge, or
/// synthesize clauses. Duplicate clauses are skipped only when their signed
/// literal set is unchanged.
pub(in crate::executor) fn take_new_theory_lemmas(
    lemmas: Vec<ay_core::TheoryLemma>,
    seen: &mut crate::incremental_proof_cache::TheoryLemmaSeenSet,
) -> (Vec<ay_core::TheoryLemma>, usize) {
    let requested = lemmas.len();
    let new_lemmas: Vec<_> = lemmas
        .into_iter()
        .filter(|lemma| seen.insert(&lemma.clause))
        .collect();
    let skipped = requested.saturating_sub(new_lemmas.len());
    (new_lemmas, skipped)
}

pub(in crate::executor) fn apply_theory_lemma_incremental(
    terms: &ay_core::TermStore,
    solver: &mut ay_sat::Solver,
    local_term_to_var: &mut super::HashMap<ay_core::TermId, u32>,
    local_var_to_term: &mut super::HashMap<u32, ay_core::TermId>,
    local_next_var: &mut u32,
    negations: &mut crate::incremental_proof_cache::IncrementalNegationCache,
    clause: &[ay_core::TheoryLit],
) -> Option<u64> {
    use ay_sat::Literal as SatLiteral;
    let lits: Vec<SatLiteral> = clause
        .iter()
        .map(|lit| {
            let var = super::ensure_incremental_atom_encoded(
                terms,
                solver,
                local_term_to_var,
                local_var_to_term,
                local_next_var,
                negations,
                lit.term,
            );
            if lit.value {
                SatLiteral::positive(var)
            } else {
                SatLiteral::negative(var)
            }
        })
        .collect();
    let before = solver.issued_original_clause_id_max();
    solver.add_clause(lits);
    single_issued_original_id_since(solver, before)
}

/// Apply a theory lemma clause to the persistent no-split incremental SAT solver.
///
/// No-split incremental lemmas must survive repeated `check-sat` calls while
/// the current SAT scope is active, but they must still disappear on `pop()`.
/// Returns whether SAT normalization retained the clause in the trace and the
/// exact original-clause ID consumed by the add. A skipped tautology still has
/// an ID so later indexed proof authorities cannot slide into its slot.
pub(in crate::executor) fn apply_theory_lemma_incremental_persistent(
    solver: &mut ay_sat::Solver,
    term_to_var: &mut super::HashMap<ay_core::TermId, u32>,
    var_to_term: &mut super::HashMap<u32, ay_core::TermId>,
    negations: &mut crate::incremental_proof_cache::IncrementalNegationCache,
    clause: &[ay_core::TheoryLit],
) -> (bool, Option<u64>) {
    use ay_sat::{Literal as SatLiteral, Variable as SatVariable};

    let mut lits: Vec<SatLiteral> = clause
        .iter()
        .map(|lit| {
            let var = *term_to_var.entry(lit.term).or_insert_with(|| {
                let next = solver.total_num_vars() as u32;
                solver.ensure_num_vars((next + 1) as usize);
                var_to_term.insert(next, lit.term);
                negations.note_fresh_term(lit.term);
                next
            });
            if lit.value {
                SatLiteral::positive(SatVariable::new(var))
            } else {
                SatLiteral::negative(SatVariable::new(var))
            }
        })
        .collect();

    if lits.is_empty() {
        let before = solver.issued_original_clause_id_max();
        solver.add_clause(lits);
        return (false, single_issued_original_id_since(solver, before));
    }

    lits.sort_by_key(|lit| lit.raw());
    lits.dedup();
    let recorded = !lits
        .windows(2)
        .any(|pair| pair[0].variable() == pair[1].variable());
    let before = solver.issued_original_clause_id_max();
    solver.add_clause(lits);
    (recorded, single_issued_original_id_since(solver, before))
}

/// Apply a string lemma clause to the incremental SAT solver.
///
/// String lemmas use TermId atoms (possibly NOT-wrapped), unlike theory
/// lemmas which use TheoryLit. This handles polarity unwrapping and
/// incremental variable encoding.
pub(in crate::executor) fn apply_string_lemma_incremental(
    terms: &ay_core::TermStore,
    solver: &mut ay_sat::Solver,
    local_term_to_var: &mut super::HashMap<ay_core::TermId, u32>,
    local_var_to_term: &mut super::HashMap<u32, ay_core::TermId>,
    local_next_var: &mut u32,
    negations: &mut crate::incremental_proof_cache::IncrementalNegationCache,
    atoms: &[ay_core::TermId],
) -> (Vec<ay_core::TermId>, Option<u64>) {
    use ay_sat::Literal as SatLiteral;
    let mut lowered_atoms = Vec::with_capacity(atoms.len());
    let mut pending: Vec<ay_core::TermId> = atoms.iter().rev().copied().collect();
    while let Some(atom) = pending.pop() {
        match terms.get(atom) {
            ay_core::term::TermData::App(ay_core::Symbol::Named(name), args)
                if name == "or" && !args.is_empty() =>
            {
                pending.extend(args.iter().rev().copied());
            }
            _ => lowered_atoms.push(atom),
        }
    }

    let lits: Vec<SatLiteral> = lowered_atoms
        .iter()
        .map(|&atom| {
            let (base_atom, positive) = match terms.get(atom) {
                ay_core::term::TermData::Not(inner) => (*inner, false),
                _ => (atom, true),
            };
            let var = super::ensure_incremental_atom_encoded(
                terms,
                solver,
                local_term_to_var,
                local_var_to_term,
                local_next_var,
                negations,
                base_atom,
            );
            if positive {
                SatLiteral::positive(var)
            } else {
                SatLiteral::negative(var)
            }
        })
        .collect();

    // Polarity hint for LengthSplit tautologies [eq, NOT(eq)]
    if lits.len() == 2
        && lits[0].variable() == lits[1].variable()
        && lits[0].is_positive() != lits[1].is_positive()
    {
        let pos_var = if lits[0].is_positive() {
            lits[0].variable()
        } else {
            lits[1].variable()
        };
        solver.set_var_phase(pos_var, true);
        for _ in 0..20 {
            solver.bump_variable_activity(pos_var);
        }
    } else if lits.len() == 2
        && lits[0].variable() != lits[1].variable()
        && lits[0].is_positive()
        && lits[1].is_positive()
    {
        let empty_idx = lowered_atoms.iter().position(|&atom| {
            if let ay_core::term::TermData::App(ay_core::Symbol::Named(name), args) =
                terms.get(atom)
            {
                name == "="
                    && args.len() == 2
                    && (matches!(
                        terms.get(args[0]),
                        ay_core::term::TermData::Const(ay_core::Constant::String(s)) if s.is_empty()
                    ) || matches!(
                        terms.get(args[1]),
                        ay_core::term::TermData::Const(ay_core::Constant::String(s)) if s.is_empty()
                    ))
            } else {
                false
            }
        });
        if let Some(ei) = empty_idx {
            let decomp_idx = 1 - ei;
            solver.set_var_phase(lits[decomp_idx].variable(), true);
            solver.set_var_phase(lits[ei].variable(), false);
            for _ in 0..10 {
                solver.bump_variable_activity(lits[decomp_idx].variable());
            }
        }
    } else if lits.len() == 3 {
        let len_eq_idx = lowered_atoms.iter().position(|&atom| {
            if let ay_core::term::TermData::App(ay_core::Symbol::Named(name), args) =
                terms.get(atom)
            {
                if name == "=" && args.len() == 2 {
                    let l_is_len = matches!(
                        terms.get(args[0]),
                        ay_core::term::TermData::App(ay_core::Symbol::Named(n), _) if n == "str.len"
                    );
                    let r_is_len = matches!(
                        terms.get(args[1]),
                        ay_core::term::TermData::App(ay_core::Symbol::Named(n), _) if n == "str.len"
                    );
                    l_is_len && r_is_len
                } else {
                    false
                }
            } else {
                false
            }
        });
        if let Some(lei) = len_eq_idx {
            solver.set_var_phase(lits[lei].variable(), true);
            for _ in 0..10 {
                solver.bump_variable_activity(lits[lei].variable());
            }
        }
    }

    // Keep fresh string-lemma atoms decision-relevant even when SAT
    // normalizes the clause away to a weak tautology.
    let mut bumped = HashSet::default();
    for lit in &lits {
        if bumped.insert(lit.variable()) {
            solver.bump_variable_activity(lit.variable());
        }
    }

    let before = solver.issued_original_clause_id_max();
    solver.add_clause(lits);
    (
        lowered_atoms,
        single_issued_original_id_since(solver, before),
    )
}

fn single_issued_original_id_since(solver: &ay_sat::Solver, before: u64) -> Option<u64> {
    let after = solver.issued_original_clause_id_max();
    if after <= before {
        return None;
    }
    let mut issued = (before + 1..=after).filter(|&id| solver.is_issued_original_clause_id(id));
    let id = issued.next()?;
    issued.next().is_none().then_some(id)
}
