// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// ---------------------------------------------------------------------------
// Direct acyclicity (occurs check) — C5b reintroduction
// ---------------------------------------------------------------------------

/// Bound on the containment walk, so an adversarial constructor DAG cannot
/// make validation super-linear: every reachable node is visited at most once
/// and the walk refuses (fail-closed) past this many nodes.
const MAX_ACYCLIC_WALK_NODES: usize = 100_000;

/// True when `needle` is a PROPER subterm of `haystack` reachable ONLY
/// through applications of registered constructors (each hop's head must be a
/// registered constructor whose result sort matches its datatype, exactly the
/// [`constructor_head`] authority the other datatype validators use).
///
/// Iterative worklist walk — no recursion, so adversarially deep constructor
/// nests cannot exhaust the native stack — with a visited set and the
/// [`MAX_ACYCLIC_WALK_NODES`] budget.
fn constructor_walk_contains(
    terms: &TermStore,
    dt_decls: DatatypeDecls<'_>,
    haystack: TermId,
    needle: TermId,
) -> bool {
    let mut pending: Vec<TermId> = vec![haystack];
    let mut visited: BTreeSet<TermId> = BTreeSet::new();
    let mut budget = MAX_ACYCLIC_WALK_NODES;
    while let Some(term) = pending.pop() {
        if !visited.insert(term) {
            continue;
        }
        if budget == 0 {
            return false;
        }
        budget -= 1;
        // Descend only through registered constructor applications: an
        // occurrence under a selector, an uninterpreted function, or any
        // other context is NOT an acyclicity violation.
        if constructor_head(terms, dt_decls, term).is_none() {
            continue;
        }
        if let TermData::App(_, args) = terms.get(term) {
            for &argument in args {
                if argument == needle {
                    return true;
                }
                pending.push(argument);
            }
        }
    }
    false
}

/// Validate a [`ay_core::TheoryLemmaKind::DatatypeAcyclicDirect`] lemma.
///
/// The clause (or-packed unit accepted) must contain SOME literal
/// `(not (= t C(..t..)))` — either equality orientation — where the other
/// side is a registered-constructor application containing `t` as a proper
/// subterm reachable only through registered constructor applications.
/// Datatype values are finite constructor trees, so `t = C(..t..)` is
/// unsatisfiable and that literal alone is valid; any additional literals
/// only weaken the clause. Fail-closed on everything else: an occurrence
/// under a selector or uninterpreted function proves nothing and is refused.
pub(crate) fn validate_datatype_acyclic_direct(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
    dt_decls: DatatypeDecls<'_>,
) -> Result<(), ProofCheckError> {
    let invalid = |reason: String| ProofCheckError::InvalidTheoryLemma {
        step: step_id,
        reason,
    };
    if clause.is_empty() {
        return Err(invalid(
            "datatype acyclicity clause must be non-empty".to_string(),
        ));
    }
    let literals = flatten_clause_literals(terms, clause);
    for &literal in &literals {
        let Some((lhs, rhs)) = negated_equality_sides(terms, literal) else {
            continue;
        };
        if terms.sort(lhs) != terms.sort(rhs) {
            continue;
        }
        for (container, contained) in [(rhs, lhs), (lhs, rhs)] {
            // The container side must itself be a registered constructor
            // application (the cycle's first hop carries the authority).
            if constructor_head(terms, dt_decls, container).is_none() {
                continue;
            }
            if constructor_walk_contains(terms, dt_decls, container, contained) {
                return Ok(());
            }
        }
    }
    Err(invalid(
        "datatype acyclicity: no literal denies an equality whose one side is a \
         registered-constructor application properly containing the other side \
         through constructor applications only"
            .to_string(),
    ))
}

/// Declaration-free recognizer (registry-parameterized): `true` exactly when
/// [`validate_datatype_acyclic_direct`] accepts the clause with these
/// registries.
#[must_use]
pub fn recognize_datatype_acyclic_direct(
    terms: &TermStore,
    clause: &[TermId],
    dt_decls: DatatypeDecls<'_>,
) -> bool {
    validate_datatype_acyclic_direct(terms, ProofId(0), clause, dt_decls).is_ok()
}

#[cfg(test)]
mod acyclic_direct_tests {
    use super::*;
    use ay_core::Symbol;

    fn list_decls() -> Vec<(String, Vec<String>)> {
        vec![(
            "List".to_string(),
            vec!["nil".to_string(), "cons".to_string()],
        )]
    }

    fn setup() -> (TermStore, TermId, TermId, Sort) {
        let mut terms = TermStore::new();
        let list_sort = Sort::Uninterpreted("List".to_string());
        let x = terms.mk_var("x", list_sort.clone());
        let zero = terms.mk_int(0.into());
        (terms, x, zero, list_sort)
    }

    #[test]
    fn accepts_direct_cycle_with_extra_literal() {
        // `(cl (not (= n 0)) (not (= x (cons 0 x))))` — the dt_occurs shape.
        let (mut terms, x, zero, list_sort) = setup();
        let n = terms.mk_var("n", Sort::Int);
        let cons = terms.mk_app(Symbol::named("cons"), vec![zero, x], list_sort);
        let cyc_eq = terms.mk_app(Symbol::named("="), vec![x, cons], Sort::Bool);
        let not_cyc = terms.mk_not(cyc_eq);
        let n_eq = terms.mk_app(Symbol::named("="), vec![n, zero], Sort::Bool);
        let not_n = terms.mk_not(n_eq);
        let decls = list_decls();
        assert!(recognize_datatype_acyclic_direct(
            &terms,
            &[not_n, not_cyc],
            &decls
        ));
    }

    #[test]
    fn accepts_nested_cycle() {
        // `x = cons(0, cons(0, x))` — two constructor hops.
        let (mut terms, x, zero, list_sort) = setup();
        let inner = terms.mk_app(Symbol::named("cons"), vec![zero, x], list_sort.clone());
        let outer = terms.mk_app(Symbol::named("cons"), vec![zero, inner], list_sort);
        let eq = terms.mk_app(Symbol::named("="), vec![outer, x], Sort::Bool);
        let not_eq = terms.mk_not(eq);
        let decls = list_decls();
        assert!(recognize_datatype_acyclic_direct(&terms, &[not_eq], &decls));
    }

    #[test]
    fn rejects_occurrence_under_selector() {
        // `x = cons(0, tl(x))` is SATISFIABLE (e.g. any cons cell whose tail
        // is shared); an occurrence under a selector proves nothing.
        let (mut terms, x, zero, list_sort) = setup();
        let tail = terms.mk_app(Symbol::named("tl"), vec![x], list_sort.clone());
        let cons = terms.mk_app(Symbol::named("cons"), vec![zero, tail], list_sort);
        let eq = terms.mk_app(Symbol::named("="), vec![x, cons], Sort::Bool);
        let not_eq = terms.mk_not(eq);
        let decls = list_decls();
        assert!(!recognize_datatype_acyclic_direct(
            &terms,
            &[not_eq],
            &decls
        ));
    }

    #[test]
    fn rejects_unregistered_constructor_lookalike() {
        // A user-declared `cons` over a DIFFERENT sort must not count: the
        // registry + result-sort authority (constructor_head) refuses it.
        let mut terms = TermStore::new();
        let other_sort = Sort::Uninterpreted("NotList".to_string());
        let x = terms.mk_var("x", other_sort.clone());
        let zero = terms.mk_int(0.into());
        let fake = terms.mk_app(Symbol::named("cons"), vec![zero, x], other_sort);
        let eq = terms.mk_app(Symbol::named("="), vec![x, fake], Sort::Bool);
        let not_eq = terms.mk_not(eq);
        let decls = list_decls();
        assert!(!recognize_datatype_acyclic_direct(
            &terms,
            &[not_eq],
            &decls
        ));
    }

    #[test]
    fn rejects_no_containment() {
        // `x = cons(0, nil)` is satisfiable.
        let (mut terms, x, zero, list_sort) = setup();
        let nil = terms.mk_var("nil", list_sort.clone());
        let cons = terms.mk_app(Symbol::named("cons"), vec![zero, nil], list_sort);
        let eq = terms.mk_app(Symbol::named("="), vec![x, cons], Sort::Bool);
        let not_eq = terms.mk_not(eq);
        let decls = list_decls();
        assert!(!recognize_datatype_acyclic_direct(
            &terms,
            &[not_eq],
            &decls
        ));
    }
}
