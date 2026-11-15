// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Propositional validity of a proof leaf, for leaves no group attributes.
//!
//! The SAT layer hands some Tseitin definitional clauses to the refutation as
//! `assume` leaves of `(or …)` when their clausification record does not
//! reach the proof manager — measured on the LRA-Lin IMC corpus as the
//! `equiv_neg2` clause `(or (= a b) a b)` of a Boolean equality in
//! `simple_startup2.3` and `tte_synchro` (the last refusal on each). Such a
//! leaf is valid by its Boolean structure alone, so the extractor may treat it
//! as a valid clause; everything else stays unclassified and fails closed.
//!
//! The check is exact and bounded: `not`, `and`, `or`, `=>`, `xor`, Boolean
//! `=` and Boolean `ite` are expanded (at most [`MAX_NODES`] nodes), every
//! other subterm is an opaque atom (at most [`MAX_ATOMS`]), and the formula
//! must hold under every assignment to the atoms. A propositional tautology
//! is valid in every theory, whatever the atoms mean.

use ay_core::term::{Constant, TermData};
use ay_core::{Sort, TermId, TermStore};

/// Opaque atoms one check may enumerate (`2^MAX_ATOMS` assignments).
const MAX_ATOMS: usize = 10;
/// Boolean connective and atom occurrences one check may expand.
const MAX_NODES: usize = 64;

/// Whether `t` holds under every assignment to its opaque atoms.
pub(super) fn is_propositional_tautology(terms: &TermStore, t: TermId) -> bool {
    let mut atoms: Vec<TermId> = Vec::new();
    let mut nodes = 0usize;
    if !collect_atoms(terms, t, &mut atoms, &mut nodes) {
        return false;
    }
    (0u32..1 << atoms.len()).all(|assignment| eval(terms, t, &atoms, assignment) == Some(true))
}

/// The Boolean-connective children of `t`, or `None` when `t` is an atom.
fn connective_children(terms: &TermStore, t: TermId) -> Option<Vec<TermId>> {
    match terms.get(t) {
        TermData::Const(Constant::Bool(_)) => Some(Vec::new()),
        TermData::Not(inner) => Some(vec![*inner]),
        TermData::Ite(c, a, b) if matches!(terms.sort(*a), Sort::Bool) => Some(vec![*c, *a, *b]),
        TermData::App(sym, args) => match sym.name() {
            "and" | "or" | "=>" | "xor" => Some(args.clone()),
            "=" if args.len() == 2 && matches!(terms.sort(args[0]), Sort::Bool) => {
                Some(args.clone())
            }
            _ => None,
        },
        _ => None,
    }
}

fn collect_atoms(terms: &TermStore, t: TermId, atoms: &mut Vec<TermId>, nodes: &mut usize) -> bool {
    *nodes += 1;
    if *nodes > MAX_NODES {
        return false;
    }
    match connective_children(terms, t) {
        Some(children) => children
            .into_iter()
            .all(|child| collect_atoms(terms, child, atoms, nodes)),
        None => {
            if !atoms.contains(&t) {
                atoms.push(t);
            }
            atoms.len() <= MAX_ATOMS
        }
    }
}

/// Value of `t` under `assignment`; `None` (the check fails closed) for an
/// atom `collect_atoms` did not record.
fn eval(terms: &TermStore, t: TermId, atoms: &[TermId], assignment: u32) -> Option<bool> {
    let value = |child: TermId| eval(terms, child, atoms, assignment);
    let all = |args: &[TermId]| -> Option<Vec<bool>> { args.iter().map(|&a| value(a)).collect() };
    Some(match terms.get(t) {
        TermData::Const(Constant::Bool(b)) => *b,
        TermData::Not(inner) => !value(*inner)?,
        TermData::Ite(c, a, b) if matches!(terms.sort(*a), Sort::Bool) => {
            if value(*c)? {
                value(*a)?
            } else {
                value(*b)?
            }
        }
        TermData::App(sym, args) if connective_children(terms, t).is_some() => {
            let values = all(args.as_slice())?;
            match sym.name() {
                "and" => values.iter().all(|&v| v),
                "or" => values.iter().any(|&v| v),
                // Right-associative: (=> a b c) = (=> a (=> b c)).
                "=>" => match values.split_last() {
                    Some((&last, premises)) => premises.iter().any(|&p| !p) || last,
                    None => true,
                },
                "xor" => values.iter().fold(false, |acc, &v| acc ^ v),
                _ => values.first()? == values.get(1)?,
            }
        }
        _ => {
            let index = atoms.iter().position(|&atom| atom == t)?;
            assignment & (1 << index) != 0
        }
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_core::Symbol;

    #[test]
    fn equiv_definitional_clauses_are_tautologies_and_their_halves_are_not() {
        let mut terms = TermStore::new();
        let a = terms.mk_var("a", Sort::Bool);
        let b = terms.mk_var("b", Sort::Bool);
        let eq = terms.mk_app(Symbol::named("="), vec![a, b], Sort::Bool);
        let not_a = terms.mk_not_raw(a);
        let not_b = terms.mk_not_raw(b);
        let or = |terms: &mut TermStore, args: Vec<TermId>| {
            terms.mk_app(Symbol::named("or"), args, Sort::Bool)
        };
        let neg2 = or(&mut terms, vec![eq, a, b]);
        let neg1 = or(&mut terms, vec![eq, not_a, not_b]);
        assert!(is_propositional_tautology(&terms, neg2));
        assert!(is_propositional_tautology(&terms, neg1));
        let half = or(&mut terms, vec![eq, a]);
        assert!(!is_propositional_tautology(&terms, half));
        // An arithmetic atom is opaque: `x <= 0 ∨ ¬(x <= 0)` is valid, the
        // arithmetic tautology `x <= 0 ∨ x >= 0` is not propositionally valid.
        let x = terms.mk_var("x", Sort::Real);
        let zero = terms.mk_int(0.into());
        let le = terms.mk_app(Symbol::named("<="), vec![x, zero], Sort::Bool);
        let ge = terms.mk_app(Symbol::named(">="), vec![x, zero], Sort::Bool);
        let not_le = terms.mk_not_raw(le);
        let excluded_middle = or(&mut terms, vec![le, not_le]);
        assert!(is_propositional_tautology(&terms, excluded_middle));
        let total = or(&mut terms, vec![le, ge]);
        assert!(!is_propositional_tautology(&terms, total));
    }

    #[test]
    fn oversized_formulas_are_refused() {
        let mut terms = TermStore::new();
        let vars: Vec<TermId> = (0..=MAX_ATOMS)
            .map(|i| terms.mk_var(format!("p{i}"), Sort::Bool))
            .collect();
        let mut lits = vars.clone();
        let not_p0 = terms.mk_not_raw(vars[0]);
        lits.push(not_p0);
        let valid_but_wide = terms.mk_app(Symbol::named("or"), lits, Sort::Bool);
        assert!(
            !is_propositional_tautology(&terms, valid_but_wide),
            "more than MAX_ATOMS atoms is refused, not enumerated"
        );
    }
}
