// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Forgery controls for the axiom-instance check and the equality swap
//! (#nested-array-checked-rung): each starts from a SATISFIABLE original
//! whose honest abstraction is uncertified, forges an instance (or a swap)
//! that only the check under test tells apart from an honest one, and shows
//! that the forged problem DOES certify UNSAT on a strict proof. Measured by
//! deleting each check in turn: the matching test goes red.

use super::*;

/// The honest instances are uncertified; `forged` replaces them and must be
/// refused by the check AND by `consume`, although a strict certificate for
/// exactly the forged problem exists (asserted).
fn assert_forged_instances_are_refused(
    script: &str,
    forge: impl FnOnce(&mut TermStore, &ArrayUfAbstraction, &[TermId]) -> Vec<TermId>,
) {
    let (mut exec, roots, abstraction, honest) = honest(script);
    assert!(!strictly_refuted(
        &mut exec,
        abstract_problem(&abstraction, &honest)
    ));
    let forged = forge(&mut exec.ctx.terms, &abstraction, &honest);
    assert!(!instances_are_valid(&exec.ctx.terms, &abstraction, &forged));
    let checked = exec
        .checked_strict_exact_unsat_solve(abstract_problem(&abstraction, &forged), 5_000)
        .expect("non-vacuity: the forged problem IS refuted on a strict proof");
    let token = CheckedArrayUfAbstractionUnsat {
        checked,
        original: roots.clone().into_boxed_slice(),
        abstraction,
        instances: forged.into_boxed_slice(),
    };
    assert!(!token.consume(&mut exec, &roots));
}

/// The fresh function the witness renamed `name` at this signature to.
fn fresh(abstraction: &ArrayUfAbstraction, name: &str, result: Sort, args: Vec<Sort>) -> Symbol {
    abstraction.witness.symbols[&(Symbol::named(name), result, args)].clone()
}

fn app_args(terms: &TermStore, term: TermId) -> Vec<TermId> {
    match terms.get(term) {
        TermData::App(_, args) => args.clone(),
        other => panic!("expected an application, got {other:?}"),
    }
}

/// A forged equality in the orientation the builder uses (TermId order), so
/// the solver can use it and the non-vacuity assertions mean something.
fn eq(terms: &mut TermStore, lhs: TermId, rhs: TermId) -> TermId {
    let args = if lhs < rhs { [lhs, rhs] } else { [rhs, lhs] };
    terms.mk_app(Symbol::named("="), args, Sort::Bool)
}

/// The side of equality `instance` applying `head`, and the other side (the
/// builder may list them in either order).
fn split(terms: &TermStore, instance: TermId, head: &Symbol) -> Option<(TermId, TermId)> {
    let [one, other] = app_args(terms, instance)[..] else {
        return None;
    };
    let applies = |term| matches!(terms.get(term), TermData::App(h, _) if h == head);
    if applies(one) {
        Some((one, other))
    } else {
        applies(other).then_some((other, one))
    }
}

fn int_array() -> Sort {
    Sort::array(Sort::Int, Sort::Int)
}

fn outer() -> Sort {
    Sort::array(Sort::Int, int_array())
}

/// Read over write without its `(= i j)` disjunct: `k = 1` makes the miss
/// false, so `m[1][0] = 7` and `c[0] = 5` collide.
#[test]
fn a_miss_instance_without_its_index_guard_is_refused() {
    assert_forged_instances_are_refused(MISS_AT_WRITTEN_INDEX, |terms, _, honest| {
        honest
            .iter()
            .map(|&instance| match terms.get(instance) {
                TermData::App(head, args) if head.name() == "or" => args[1],
                _ => instance,
            })
            .collect()
    });
}

/// The honest miss instance `(or (= i j) (= (R W j) (R a j)))` of `script`,
/// rebuilt by `forge` from its parts `[i, j, W, a]`; the other instances stay.
fn forge_miss(
    script: &str,
    forge: impl Fn(&mut TermStore, &ArrayUfAbstraction, [TermId; 4]) -> [TermId; 4],
) {
    assert_forged_instances_are_refused(script, |terms, abstraction, honest| {
        let select = fresh(abstraction, "select", int_array(), vec![outer(), Sort::Int]);
        let store = fresh(
            abstraction,
            "store",
            outer(),
            vec![outer(), Sort::Int, int_array()],
        );
        let applies = |term: TermId, head: &Symbol| matches!(terms.get(term), TermData::App(h, _) if h == head);
        let miss = honest
            .iter()
            .copied()
            .find(|&instance| {
                app_args(terms, instance).len() == 2 && !applies(instance, &Symbol::named("="))
            })
            .expect("the miss instance");
        let differ = app_args(terms, miss)[1];
        let above = app_args(terms, differ)
            .into_iter()
            .find(|&side| applies(side, &select) && applies(app_args(terms, side)[0], &store))
            .expect("a read of the write");
        let [write, other] = app_args(terms, above)[..] else {
            unreachable!("a read")
        };
        let [base, index, _] = app_args(terms, write)[..] else {
            unreachable!("a store")
        };
        let element = terms.sort(above).clone();
        let [index, other, write, base] = forge(terms, abstraction, [index, other, write, base]);
        let same = eq(terms, index, other);
        let read = terms.mk_app(select.clone(), [write, other], element.clone());
        let below = terms.mk_app(select, [base, other], element);
        let differ = eq(terms, read, below);
        let forged = terms.mk_app(Symbol::named("or"), [same, differ], Sort::Bool);
        honest
            .iter()
            .map(|&instance| if instance == miss { forged } else { instance })
            .collect()
    });
}

/// Read over write guarded by an index OTHER than the written one. Under
/// `k = 1` the write is read at its own index, so `c[0] != m[1][0]` is
/// satisfiable (z3: `sat`); the forged guard `(= 0 k)` is false and forces
/// `W[k] = m[k]`, contradicting the disequality.
#[test]
fn a_miss_instance_guarded_by_another_index_is_refused() {
    const SCRIPT: &str = "\
        (declare-const m (Array Int (Array Int Int)))(declare-const c (Array Int Int))\
        (declare-const k Int)(assert (= k 1))\
        (assert (not (= (select (select (store m 1 c) k) 0) (select (select m k) 0))))";
    forge_miss(SCRIPT, |terms, _, [_, other, write, base]| {
        [terms.mk_int(0.into()), other, write, base]
    });
}

/// Read over write falling through to an array OTHER than the written base.
/// Under `k = 2`, `m[2][0] != n[2][0]` is satisfiable (z3: `sat`); the forged
/// `W[k] = n[k]` contradicts it.
#[test]
fn a_miss_instance_reading_another_base_is_refused() {
    const SCRIPT: &str = "\
        (declare-const m (Array Int (Array Int Int)))(declare-const n (Array Int (Array Int Int)))\
        (declare-const c (Array Int Int))(declare-const k Int)(assert (= k 2))\
        (assert (not (= (select (select (store m 1 c) k) 0) (select (select n k) 0))))";
    forge_miss(SCRIPT, |terms, abstraction, [index, other, write, _]| {
        let n = abstraction.witness.vars[&terms.find_var("n").expect("n")];
        [index, other, write, n]
    });
}

/// Selector over constructor at the WRONG field of the same sort.
#[test]
fn a_selector_instance_at_another_field_is_refused() {
    assert_forged_instances_are_refused(SAME_SORTED_FIELDS, |terms, abstraction, honest| {
        assert_eq!(honest.len(), 1, "l over mk");
        let p = Sort::Uninterpreted("P".to_string());
        let l = fresh(abstraction, "l", int_array(), vec![p]);
        let (projected, _x) = split(terms, honest[0], &l).expect("l over mk");
        let constructed = app_args(terms, projected)[0];
        let y = app_args(terms, constructed)[1];
        vec![eq(terms, projected, y)]
    });
}

/// Selector over constructor for a selector of the OTHER constructor.
#[test]
fn a_selector_instance_of_a_foreign_constructor_is_refused() {
    assert_forged_instances_are_refused(FOREIGN_SELECTOR, |terms, abstraction, honest| {
        assert!(honest.is_empty(), "no selector of `A` is ever read");
        let dt = |name: &str| Sort::Uninterpreted(name.to_string());
        let (e, arrays) = (dt("E"), int_array());
        let a_ctor = fresh(abstraction, "A", e.clone(), vec![arrays.clone()]);
        let fb = fresh(abstraction, "fb", arrays.clone(), vec![e]);
        let image = |s: &Sort| abstraction.witness.sorts[s].clone();
        let x = abstraction.witness.vars[&terms.find_var("x").expect("x")];
        let constructed = terms.mk_app(a_ctor, [x], image(&dt("E")));
        let projected = terms.mk_app(fb, [constructed], image(&arrays));
        vec![eq(terms, projected, x)]
    });
}

/// Read over constant with a value other than the constant's.
#[test]
fn a_constant_instance_with_another_value_is_refused() {
    assert_forged_instances_are_refused(CONSTANT_READ, |terms, abstraction, honest| {
        assert_eq!(honest.len(), 1, "the outer constant read at 0");
        let select = fresh(abstraction, "select", int_array(), vec![outer(), Sort::Int]);
        let (read, _c) = split(terms, honest[0], &select).expect("a read of the constant");
        let d = abstraction.witness.vars[&terms.find_var("d").expect("d")];
        vec![eq(terms, read, d)]
    });
}

/// Read over write "hit" at an index other than the written one, beside the
/// honest instances (the inner constant read supplies the contradiction).
#[test]
fn a_hit_instance_at_another_index_is_refused() {
    assert_forged_instances_are_refused(READ_ELSEWHERE, |terms, abstraction, honest| {
        let select = fresh(abstraction, "select", int_array(), vec![outer(), Sort::Int]);
        let image = abstraction.witness.sorts[&int_array()].clone();
        let (lhs, value) = honest
            .iter()
            .find_map(|&instance| split(terms, instance, &select))
            .expect("the hit instance");
        let write = app_args(terms, lhs)[0];
        let k = terms.find_var("k").expect("k");
        let elsewhere = terms.mk_app(select, [write, k], image);
        let forged = eq(terms, elsewhere, value);
        honest.iter().copied().chain([forged]).collect()
    });
}

/// Canonical orientation: the builder lists a binary `=`'s image arguments in
/// the TermId order `mk_eq` interns (the solver finds an equality atom only
/// in that orientation), and the witness marks each swap. The checker admits
/// a swap on binary `=` alone. Forgery: mark the kept `(f x y)` swapped and
/// image it `(f y x)`, turning satisfiable `f(x,y), not f(y,x)` into a
/// propositional contradiction.
#[test]
fn a_swap_on_a_head_other_than_equality_is_refused() {
    const SCRIPT: &str = "\
        (declare-const u (Array Int (Array Int Int)))(declare-const v (Array Int Int))\
        (declare-fun f (Int Int) Bool)(declare-const x Int)(declare-const y Int)\
        (assert (= (select u 0) v))(assert (f x y))(assert (not (f y x)))";
    let (mut exec, roots, mut abstraction) = built(SCRIPT);
    assert!(is_pure_renaming(&exec.ctx.terms, &roots, &abstraction));
    assert!(!strictly_refuted(&mut exec, abstraction.roots().to_vec()));
    let (x, y) = (var_named(&exec, "x"), var_named(&exec, "y"));
    let applied = roots[1];
    assert_eq!(app_args(&exec.ctx.terms, applied), vec![x, y], "(f x y)");
    let flipped = exec
        .ctx
        .terms
        .mk_app(Symbol::named("f"), [y, x], Sort::Bool);
    let mut forged_roots = abstraction.roots().to_vec();
    forged_roots[1] = flipped;
    abstraction.witness.swapped.insert(applied);
    let forged = ArrayUfAbstraction {
        roots: forged_roots.into_boxed_slice(),
        witness: abstraction.witness,
    };
    assert!(!is_pure_renaming(&exec.ctx.terms, &roots, &forged));
    let checked = exec
        .checked_strict_exact_unsat_solve(forged.roots().to_vec(), 5_000)
        .expect("non-vacuity: `f(y,x), not f(y,x)` is refuted on a strict proof");
    let token = CheckedArrayUfAbstractionUnsat {
        checked,
        original: roots.clone().into_boxed_slice(),
        abstraction: forged,
        instances: Box::default(),
    };
    assert!(!token.consume(&mut exec, &roots));
}

/// The positive side of the same rule: an abstraction whose equalities were
/// swapped into canonical order is still a pure renaming, and each swap sits
/// on a binary `=`.
#[test]
fn every_recorded_swap_is_a_binary_equality() {
    let (exec, roots, abstraction) = built(&script_body(VEC_ANCESTOR));
    assert!(is_pure_renaming(&exec.ctx.terms, &roots, &abstraction));
    assert!(
        !abstraction.witness.swapped.is_empty(),
        "the ancestor row puts at least one equality image into canonical order"
    );
    for &node in &abstraction.witness.swapped {
        let TermData::App(head, args) = exec.ctx.terms.get(node) else {
            panic!("a swap on a non-application");
        };
        assert!(build::is_binary_equality(
            head,
            args,
            exec.ctx.terms.sort(node)
        ));
    }
}
