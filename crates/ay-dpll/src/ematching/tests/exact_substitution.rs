// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

/// Producer/checker metering parity: the strict checker walks every occurrence
/// of a shared DAG subtree. The exact producer must fail closed at the same
/// 100k structural-work boundary instead of charging only distinct term IDs and
/// emitting an artifact the checker cannot finish validating.
#[test]
fn exact_substitution_meters_repeated_dag_edges_like_the_checker() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("metered_exact_x", Sort::Int);
    let r_x = terms.mk_app(Symbol::named("metered_exact_r"), [x], Sort::Int);
    let q_r_x = terms.mk_app(Symbol::named("metered_exact_q"), [r_x], Sort::Int);
    let p_q_r_x = terms.mk_app(Symbol::named("metered_exact_p"), [q_r_x], Sort::Bool);
    let repeated = vec![p_q_r_x; 25_000];
    let body = terms.mk_app(Symbol::named("and"), repeated, Sort::Bool);
    let zero = terms.mk_int(BigInt::from(0));
    let mut substitution = HashMap::default();
    substitution.insert("metered_exact_x".to_string(), zero);

    assert!(
        subst_vars_exact_qf(&mut terms, body, &substitution).is_none(),
        "repeated DAG edges above the strict checker's work budget must fail closed"
    );
}

/// REGRESSION for the deductive-checks `Unknown((incomplete self-check-rejected))`
/// class: a quantifier whose binder SPELLING is also a live ambient symbol,
/// re-instantiated at that ambient symbol.
///
/// `forall ((self S)) (or (not (lt0 self)) (m self))` over a binder-free body,
/// witness `self` — the `declare-const self` the binder shadows. The
/// instantiation is `∀x. φ(x) ⊢ φ(c)` with `c` the ambient constant, and the
/// result has no binder in it at all, so nothing can capture. The blanket
/// source-binder spelling test refused this outright and cost the whole UNSAT
/// certificate.
#[test]
fn exact_substitution_accepts_a_shadowed_ambient_witness_in_a_binder_free_body() {
    let mut terms = TermStore::new();
    let sort = Sort::Uninterpreted("shadow_amb_S".to_string());
    let bound = terms.mk_var("shadow_amb_self", sort.clone());
    let lt0 = terms.mk_app(Symbol::named("shadow_amb_lt0"), [bound], Sort::Bool);
    let not_lt0 = terms.mk_not_raw(lt0);
    let m = terms.mk_app(Symbol::named("shadow_amb_m"), [bound], Sort::Bool);
    let body = terms.mk_app(Symbol::named("or"), [not_lt0, m], Sort::Bool);
    let mut substitution = HashMap::default();
    substitution.insert("shadow_amb_self".to_string(), bound);

    assert_eq!(
        subst_vars_exact_qf(&mut terms, body, &substitution),
        Some(body),
        "instantiating a binder-free body at the ambient symbol it shadows is capture-free"
    );
}

/// The same shape with a DIFFERENT ambient identity behind the same spelling:
/// still capture-free, because the instance is still binder-free.
#[test]
fn exact_substitution_accepts_a_distinct_same_spelled_witness_in_a_binder_free_body() {
    let mut terms = TermStore::new();
    let bound = terms.mk_var("shadow_id_x", Sort::Int);
    let ambient = terms.mk_fresh_named_var("shadow_id_x", Sort::Int);
    assert_ne!(bound, ambient);
    let body = terms.mk_app(Symbol::named("shadow_id_p"), [bound], Sort::Bool);
    let expected = terms.mk_app(Symbol::named("shadow_id_p"), [ambient], Sort::Bool);
    let mut substitution = HashMap::default();
    substitution.insert("shadow_id_x".to_string(), ambient);

    assert_eq!(
        subst_vars_exact_qf(&mut terms, body, &substitution),
        Some(expected),
        "a binder-free instance cannot capture, whatever the witness is spelled"
    );
}

/// The narrowed guard still refuses the capture it exists for: the body
/// RE-BINDS the source spelling, so that spelling is back in scope over a
/// substitution site and the witness would be captured there.
///
/// `forall ((x Int)) (and (p x) (forall ((x Int)) (q x)))` with witness `x`:
/// accepting it would emit an instance whose second conjunct still reads
/// `(forall ((x Int)) (q x))` while the first now carries a free `x` that the
/// checker cannot tell from the re-bound one.
#[test]
fn exact_substitution_refuses_a_witness_named_by_a_binder_the_body_rebinds() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("rebind_x", Sort::Int);
    let p_x = terms.mk_app(Symbol::named("rebind_p"), [x], Sort::Bool);
    let q_x = terms.mk_app(Symbol::named("rebind_q"), [x], Sort::Bool);
    let inner = terms.mk_forall(vec![("rebind_x".to_string(), Sort::Int)], q_x);
    let body = terms.mk_app(Symbol::named("and"), [p_x, inner], Sort::Bool);
    let mut substitution = HashMap::default();
    substitution.insert("rebind_x".to_string(), x);

    assert!(
        subst_vars_exact_qf(&mut terms, body, &substitution).is_none(),
        "a source spelling the body re-binds is still in scope and must fail closed"
    );
}

/// The nested-binder capture the widening was written for is untouched: the
/// witness names the INNER binder, so it lands under a binder of its own name.
#[test]
fn exact_substitution_still_refuses_a_witness_named_by_a_nested_binder() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("nested_guard_x", Sort::Int);
    let y = terms.mk_var("nested_guard_y", Sort::Int);
    let p_xy = terms.mk_app(Symbol::named("nested_guard_p"), [x, y], Sort::Bool);
    let body = terms.mk_forall(vec![("nested_guard_y".to_string(), Sort::Int)], p_xy);
    let mut substitution = HashMap::default();
    substitution.insert("nested_guard_x".to_string(), y);

    assert!(
        subst_vars_exact_qf(&mut terms, body, &substitution).is_none(),
        "a witness spelled like the inner binder must stay refused"
    );
}

/// The newly-admitted lane is SIMULTANEOUS substitution, and this pins that
/// down: `{a := b, b := c}` on `P(a, b)` is `P(b, c)`, never the sequential
/// `P(c, c)`. `visit` splices each replacement in verbatim and never re-walks
/// it, so a replacement spelled like another source binder denotes the ambient
/// symbol, exactly as the substitution lemma requires.
#[test]
fn exact_substitution_is_simultaneous_when_a_replacement_names_another_binder() {
    let mut terms = TermStore::new();
    let sort = Sort::Uninterpreted("simul_S".to_string());
    let a = terms.mk_var("simul_a", sort.clone());
    let b = terms.mk_var("simul_b", sort.clone());
    let c = terms.mk_var("simul_c", sort.clone());
    let body = terms.mk_app(Symbol::named("simul_p"), [a, b], Sort::Bool);
    let expected = terms.mk_app(Symbol::named("simul_p"), [b, c], Sort::Bool);
    let sequential = terms.mk_app(Symbol::named("simul_p"), [c, c], Sort::Bool);
    let mut substitution = HashMap::default();
    substitution.insert("simul_a".to_string(), b);
    substitution.insert("simul_b".to_string(), c);

    let instance = subst_vars_exact_qf(&mut terms, body, &substitution)
        .expect("a binder-free body admits a replacement spelled like a sibling binder");
    assert_eq!(
        instance, expected,
        "the exact walker must not re-substitute"
    );
    assert_ne!(instance, sequential);
}
