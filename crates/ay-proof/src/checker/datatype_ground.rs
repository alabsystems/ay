// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Ground datatype/EUF conflict-clause validation (#dt-ground-conflict).
//!
//! Mid-solve DPLL(T) theory conflicts and propagation explanations enter the
//! SAT trace as ORIGINAL clauses — multi-literal disjunctions such as
//! `(or (not (= a b)) (not (= c d)) ..)` (an equality chain closing a
//! constructor cycle) or `(or (= x C(..)) (not (= ..)) ..)` (an entailed
//! equality under premises). None of the single-schema datatype validators
//! accept these, so they previously stayed `Generic` trust and blocked
//! certification (#trust->0).
//!
//! This module validates the whole family at once with an INDEPENDENT bounded
//! ground decision procedure: a clause is a theory tautology exactly when the
//! conjunction of its negated literals is unsatisfiable. The refuter assumes
//! the negated literals and closes under a fixed set of individually sound
//! ground inference rules:
//!
//!  * congruence closure (union-find + signature matching over the subterm
//!    universe, `not`/`ite` treated as ordinary operators);
//!  * Boolean semantics of `not` and of equality atoms (an equality atom is
//!    TRUE when its sides are merged; a TRUE equality atom merges its sides;
//!    a FALSE one records a disequality);
//!  * datatype constructor CLASH (two registered constructor heads of the
//!    same datatype with different constructors in one class);
//!  * constructor INJECTIVITY (same registered constructor in one class
//!    merges corresponding arguments);
//!  * tester EVALUATION (a registered tester on a constructor-headed class
//!    is TRUE/FALSE by constructor identity) and tester EXCLUSIVITY (two
//!    TRUE testers for distinct registered siblings on one subject class);
//!  * selector PROJECTION (a registered field-`i` selector on a class
//!    containing a full application of its constructor merges with argument
//!    `i`);
//!  * structural ACYCLICITY (a directed cycle in the class graph whose edges
//!    go from a class through a registered constructor-application member to
//!    its argument classes refutes: a constructor value is a finite tree, so
//!    no value properly contains itself).
//!
//! Contradiction is reached when TRUE and FALSE merge, a recorded
//! disequality's sides merge, or a clash/exclusivity/acyclicity rule fires.
//!
//! SOUNDNESS. Every rule above is a valid inference of datatype theory with
//! equality: each merge it performs is entailed by the assumed facts in every
//! model, and each contradiction rule refutes a genuinely unsatisfiable
//! configuration. Hence if the refuter reports contradiction, the negated
//! literals are jointly unsatisfiable and the clause is VALID. The converse
//! direction is deliberately incomplete and fail-closed: budget exhaustion,
//! non-ground constructs (binders), or a fixpoint without contradiction all
//! REJECT. Constructor/tester/selector identity is re-derived from the
//! declaration registries on every use — term shape alone is never trusted.

use ay_core::{ProofId, TermData, TermId, TermStore};

use super::datatype_axiom::{flatten_clause_literals, DatatypeDecls, SelectorDecls};
use super::ProofCheckError;

mod cycle;
mod refuter;

use refuter::GroundRefuter;

/// Hard cap on saturation rounds. Every productive round merges classes in a
/// bounded universe, so the refuter terminates before this backstop in practice.
const MAX_GROUND_ROUNDS: usize = 4096;

/// Validate a `DatatypeGroundConflict` lemma in strict mode against the
/// datatype AND constructor→selector registries: the clause is accepted
/// exactly when the bounded ground refuter derives a contradiction from the
/// conjunction of its negated literals (see the module doc for the rule set
/// and the soundness argument). Fail-closed on binders, budget exhaustion,
/// and saturation without contradiction.
pub(crate) fn validate_datatype_ground_conflict(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
    dt_decls: DatatypeDecls<'_>,
    ctor_selectors: SelectorDecls<'_>,
) -> Result<(), ProofCheckError> {
    let invalid = |reason: String| ProofCheckError::InvalidTheoryLemma {
        step: step_id,
        reason,
    };
    if clause.is_empty() {
        return Err(invalid(
            "datatype ground-conflict clause must be non-empty".to_string(),
        ));
    }
    let literals = flatten_clause_literals(terms, clause);

    let mut refuter = GroundRefuter::new(terms, dt_decls, ctor_selectors);

    // Negate the clause: assume the opposite polarity of every literal.
    let mut atoms: Vec<TermId> = Vec::new();
    let mut polarities: Vec<(TermId, bool)> = Vec::new();
    for &literal in &literals {
        match terms.get(literal) {
            TermData::Not(inner) => {
                atoms.push(*inner);
                polarities.push((*inner, true));
            }
            _ => {
                atoms.push(literal);
                polarities.push((literal, false));
            }
        }
    }
    if refuter.collect_universe(&atoms).is_err() {
        return Err(invalid(
            "datatype ground-conflict refuter: non-ground construct or node budget exceeded"
                .to_string(),
        ));
    }
    for (atom, polarity) in polarities {
        refuter.assume(atom, polarity);
    }

    for _ in 0..MAX_GROUND_ROUNDS {
        let mut changed = false;
        if refuter.round(&mut changed) {
            return Ok(());
        }
        if !changed {
            break;
        }
    }
    Err(invalid(
        "datatype ground-conflict refuter reached saturation without contradiction; \
         the clause is not certified as a ground theory tautology"
            .to_string(),
    ))
}

/// Recognize whether `clause` is a valid ground datatype/EUF conflict clause
/// under the given registries — i.e. whether
/// `validate_datatype_ground_conflict` would accept it. Because it IS the
/// strict validator, classifier and checker cannot drift.
#[must_use]
pub fn recognize_datatype_ground_conflict(
    terms: &TermStore,
    clause: &[TermId],
    dt_decls: &[(String, Vec<String>)],
    ctor_selectors: &[(String, Vec<String>)],
) -> bool {
    validate_datatype_ground_conflict(terms, ProofId(0), clause, dt_decls, ctor_selectors).is_ok()
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_core::{Sort, Symbol};

    type Registry = Vec<(String, Vec<String>)>;

    fn registries() -> (Registry, Registry) {
        (
            vec![(
                "Tower".to_string(),
                vec!["stack".to_string(), "empty".to_string()],
            )],
            vec![
                (
                    "stack".to_string(),
                    vec!["top".to_string(), "rest".to_string()],
                ),
                ("empty".to_string(), vec![]),
            ],
        )
    }

    fn eq(terms: &mut TermStore, a: TermId, b: TermId) -> TermId {
        terms.mk_app(Symbol::named("="), vec![a, b], Sort::Bool)
    }

    #[test]
    fn accepts_equality_chain_constructor_cycle() {
        // `x = stack(h, y)` and `y = x` close a structural cycle; the clause
        // `(or (not (= x (stack h y))) (not (= y x)))` is therefore valid.
        let (decls, sels) = registries();
        let mut terms = TermStore::new();
        let tower = Sort::Uninterpreted("Tower".to_string());
        let x = terms.mk_var("x", tower.clone());
        let y = terms.mk_var("y", tower.clone());
        let h = terms.mk_var("h", Sort::Int);
        let st = terms.mk_app(Symbol::named("stack"), vec![h, y], tower);
        let eq1 = eq(&mut terms, x, st);
        let eq2 = eq(&mut terms, y, x);
        let l1 = terms.mk_not(eq1);
        let l2 = terms.mk_not(eq2);
        assert!(recognize_datatype_ground_conflict(
            &terms,
            &[l1, l2],
            &decls,
            &sels
        ));
        // Dropping the linking equality leaves a satisfiable assumption set:
        // the single-literal remainder is NOT valid.
        assert!(!recognize_datatype_ground_conflict(
            &terms,
            &[l1],
            &decls,
            &sels
        ));
    }

    #[test]
    fn accepts_constructor_clash_through_chain() {
        // `x = stack(h, y)`, `x = z`, `z = empty` is a clash.
        let (decls, sels) = registries();
        let mut terms = TermStore::new();
        let tower = Sort::Uninterpreted("Tower".to_string());
        let x = terms.mk_var("x", tower.clone());
        let y = terms.mk_var("y", tower.clone());
        let z = terms.mk_var("z", tower.clone());
        let h = terms.mk_var("h", Sort::Int);
        let st = terms.mk_app(Symbol::named("stack"), vec![h, y], tower.clone());
        let empty = terms.mk_app(Symbol::named("empty"), vec![], tower);
        let eq1 = eq(&mut terms, x, st);
        let eq2 = eq(&mut terms, x, z);
        let eq3 = eq(&mut terms, z, empty);
        let clause: Vec<TermId> = [eq1, eq2, eq3]
            .into_iter()
            .map(|e| terms.mk_not(e))
            .collect();
        assert!(recognize_datatype_ground_conflict(
            &terms, &clause, &decls, &sels
        ));
    }

    #[test]
    fn accepts_entailed_equality_conclusion() {
        // Injectivity: `stack(a, r1) = stack(b, r2)` entails `a = b`, so
        // `(or (= a b) (not (= (stack a r1) (stack b r2))))` is valid.
        let (decls, sels) = registries();
        let mut terms = TermStore::new();
        let tower = Sort::Uninterpreted("Tower".to_string());
        let a = terms.mk_var("a", Sort::Int);
        let b = terms.mk_var("b", Sort::Int);
        let r1 = terms.mk_var("r1", tower.clone());
        let r2 = terms.mk_var("r2", tower.clone());
        let s1 = terms.mk_app(Symbol::named("stack"), vec![a, r1], tower.clone());
        let s2 = terms.mk_app(Symbol::named("stack"), vec![b, r2], tower);
        let eq_ctor = eq(&mut terms, s1, s2);
        let eq_ab = eq(&mut terms, a, b);
        let not_ctor = terms.mk_not(eq_ctor);
        assert!(recognize_datatype_ground_conflict(
            &terms,
            &[eq_ab, not_ctor],
            &decls,
            &sels
        ));
        // The converse — concluding an UNRELATED equality — must fail.
        let c = terms.mk_var("c", Sort::Int);
        let eq_ac = eq(&mut terms, a, c);
        assert!(!recognize_datatype_ground_conflict(
            &terms,
            &[eq_ac, not_ctor],
            &decls,
            &sels
        ));
    }

    #[test]
    fn accepts_tester_conflict_and_selector_projection() {
        // `is-empty(x)` with `x = stack(h, r)` is a tester conflict.
        let (decls, sels) = registries();
        let mut terms = TermStore::new();
        let tower = Sort::Uninterpreted("Tower".to_string());
        let x = terms.mk_var("x", tower.clone());
        let h = terms.mk_var("h", Sort::Int);
        let r = terms.mk_var("r", tower.clone());
        let st = terms.mk_app(Symbol::named("stack"), vec![h, r], tower.clone());
        let is_empty_x = terms.mk_app(Symbol::named("is-empty"), vec![x], Sort::Bool);
        let eq1 = eq(&mut terms, x, st);
        let not_eq1 = terms.mk_not(eq1);
        let not_tester = terms.mk_not(is_empty_x);
        assert!(recognize_datatype_ground_conflict(
            &terms,
            &[not_eq1, not_tester],
            &decls,
            &sels
        ));

        // Selector projection: `x = stack(h, r)` entails `top(x) = h`.
        let top_x = terms.mk_app(Symbol::named("top"), vec![x], Sort::Int);
        let eq_top = eq(&mut terms, top_x, h);
        assert!(recognize_datatype_ground_conflict(
            &terms,
            &[eq_top, not_eq1],
            &decls,
            &sels
        ));
    }

    #[test]
    fn rejects_unregistered_constructor_and_saturation() {
        // The same cycle over an UNREGISTERED constructor symbol proves
        // nothing — `stack2` carries no structural authority.
        let (decls, sels) = registries();
        let mut terms = TermStore::new();
        let tower = Sort::Uninterpreted("Tower".to_string());
        let x = terms.mk_var("x", tower.clone());
        let h = terms.mk_var("h", Sort::Int);
        let st = terms.mk_app(Symbol::named("stack2"), vec![h, x], tower);
        let eq1 = eq(&mut terms, x, st);
        let l1 = terms.mk_not(eq1);
        assert!(!recognize_datatype_ground_conflict(
            &terms,
            &[l1],
            &decls,
            &sels
        ));
        // And with an empty registry even the registered spelling fails.
        assert!(!recognize_datatype_ground_conflict(&terms, &[l1], &[], &[]));
    }

    #[test]
    fn accepts_boolean_branch_implication_elimination() {
        // The Boolean-consequence premise shape (#dt-context-derivation):
        // `(cl P (not c) (not B))` where `B = (or (not c) (and P Q))` — the
        // authored-ITE then-implication. Negated: {¬P, c, B}; or-elimination
        // under c forces the `and`, whose conjunct P contradicts ¬P.
        let (decls, sels) = registries();
        let mut terms = TermStore::new();
        let tower = Sort::Uninterpreted("Tower".to_string());
        let x = terms.mk_var("x", tower.clone());
        let y = terms.mk_var("y", tower.clone());
        let z = terms.mk_var("z", tower);
        let c = terms.mk_var("c", Sort::Bool);
        let p = eq(&mut terms, x, y);
        let q = eq(&mut terms, y, z);
        let conjunction = terms.mk_app(Symbol::named("and"), vec![p, q], Sort::Bool);
        let not_c = terms.mk_not(c);
        let branch = terms.mk_app(Symbol::named("or"), vec![not_c, conjunction], Sort::Bool);
        let not_branch = terms.mk_not(branch);
        let clause = [p, not_c, not_branch];
        assert!(recognize_datatype_ground_conflict(
            &terms, &clause, &decls, &sels
        ));
        // Without the guard the branch alone decides nothing.
        assert!(!recognize_datatype_ground_conflict(
            &terms,
            &[p, not_branch],
            &decls,
            &sels
        ));
        // And the else-side dual: `B_else = (or c Q)` with guard FALSE.
        let branch_else = terms.mk_app(Symbol::named("or"), vec![c, q], Sort::Bool);
        let not_branch_else = terms.mk_not(branch_else);
        let clause_else = [q, c, not_branch_else];
        assert!(recognize_datatype_ground_conflict(
            &terms,
            &clause_else,
            &decls,
            &sels
        ));
    }

    #[test]
    fn accepts_nested_ite_chain_elimination() {
        // The blocksworld transition shape: `imp_else = (or c1 (ite c2 P Q))`
        // with the outer guard FALSE and the inner guard TRUE selects P.
        // Clause: `(cl P (not (not c1)) (not c2) (not imp_else))` — i.e. the
        // conjunct follows from {¬c1, c2, imp_else}.
        let (decls, sels) = registries();
        let mut terms = TermStore::new();
        let tower = Sort::Uninterpreted("Tower".to_string());
        let x = terms.mk_var("x", tower.clone());
        let y = terms.mk_var("y", tower.clone());
        let z = terms.mk_var("z", tower);
        let c1 = terms.mk_var("c1", Sort::Bool);
        let c2 = terms.mk_var("c2", Sort::Bool);
        let p = eq(&mut terms, x, y);
        let q = eq(&mut terms, y, z);
        let inner = terms.mk_ite(c2, p, q);
        let imp_else = terms.mk_app(Symbol::named("or"), vec![c1, inner], Sort::Bool);
        let not_c1 = terms.mk_not(c1);
        let not_not_c1 = terms.mk_not(not_c1);
        let not_c2 = terms.mk_not(c2);
        let not_imp_else = terms.mk_not(imp_else);
        assert!(recognize_datatype_ground_conflict(
            &terms,
            &[p, not_not_c1, not_c2, not_imp_else],
            &decls,
            &sels
        ));
        // The inner-else dual: with c2 FALSE the chain selects Q.
        let clause_q = [q, not_not_c1, c2, not_imp_else];
        assert!(recognize_datatype_ground_conflict(
            &terms, &clause_q, &decls, &sels
        ));
        // Undecided inner guard: nothing selects a branch; fail closed.
        assert!(!recognize_datatype_ground_conflict(
            &terms,
            &[p, not_not_c1, not_imp_else],
            &decls,
            &sels
        ));
    }

    #[test]
    fn accepts_pure_euf_congruence_conflict() {
        // `a = b` entails `f(a) = f(b)`: the clause
        // `(or (not (= a b)) (= (f a) (f b)))` is valid by congruence.
        let (decls, sels) = registries();
        let mut terms = TermStore::new();
        let a = terms.mk_var("a", Sort::Int);
        let b = terms.mk_var("b", Sort::Int);
        let fa = terms.mk_app(Symbol::named("f"), vec![a], Sort::Int);
        let fb = terms.mk_app(Symbol::named("f"), vec![b], Sort::Int);
        let eq_ab = eq(&mut terms, a, b);
        let eq_f = eq(&mut terms, fa, fb);
        let not_ab = terms.mk_not(eq_ab);
        assert!(recognize_datatype_ground_conflict(
            &terms,
            &[not_ab, eq_f],
            &decls,
            &sels
        ));
    }
}
