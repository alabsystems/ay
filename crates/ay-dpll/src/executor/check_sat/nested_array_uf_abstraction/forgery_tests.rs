// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Forgery controls for [`is_pure_renaming`]: one per check that stops the
//! abstraction from being STRONGER than the original (root count, plain leaf
//! identity, kept-head identity, arity, image sort, witness image,
//! unclassified head, binder list, uninterpreted fresh sort, minted fresh
//! function).
//!
//! Each starts from a SATISFIABLE original whose honest abstraction is a pure
//! renaming and has no certificate, forges a strengthened abstraction that
//! only the check under test can tell apart from the honest one, and (except
//! for the minted-function control, see there) shows that the forgery DOES
//! certify UNSAT on a strict proof. So the check is the only thing between a
//! satisfiable problem and a published `unsat`: delete it and the matching
//! test goes red. Measured by deleting each check in turn; the checks with no
//! test here are redundant with another check or cannot strengthen (trigger
//! shapes, the node cap, the final array-freedom re-check).

use super::*;

/// The honest abstraction of `roots` is a pure renaming and yields no strict
/// certificate: the positive control every forgery test starts from.
fn assert_honest_abstraction_is_uncertified(script: &str) {
    let (mut exec, roots, honest) = built(script);
    assert!(
        is_pure_renaming(&exec.ctx.terms, &roots, &honest),
        "positive control: the honest abstraction is a pure renaming"
    );
    assert!(
        exec.checked_strict_exact_unsat_solve(honest.roots().to_vec(), 5_000)
            .is_none(),
        "positive control: the satisfiable original's abstraction certifies nothing"
    );
}

/// `forged` must be refused by the checker AND by `consume`, although a strict
/// certificate for exactly its roots exists (asserted, so the refusal is not
/// vacuous).
fn assert_certified_forgery_is_refused(
    exec: &mut Executor,
    roots: &[TermId],
    forged: ArrayUfAbstraction,
) {
    assert!(
        !is_pure_renaming(&exec.ctx.terms, roots, &forged),
        "the forged abstraction must not pass as a renaming"
    );
    let checked = exec
        .checked_strict_exact_unsat_solve(forged.roots().to_vec(), 5_000)
        .expect("non-vacuity: the forged abstraction IS refuted on a strict proof");
    let token = CheckedArrayUfAbstractionUnsat {
        checked,
        original: roots.into(),
        abstraction: forged,
        instances: Box::default(),
    };
    assert!(
        !token.consume(exec, roots),
        "a strict certificate for a forgery must not become UNSAT authority for a SAT original"
    );
}

/// Rebuild application `term` with `head` and `args`, via the raw constructor.
fn rebuild_app(terms: &mut TermStore, term: TermId, head: Symbol, args: &[TermId]) -> TermId {
    let sort = terms.sort(term).clone();
    terms.mk_app(head, args, sort)
}

fn app_args(terms: &TermStore, term: TermId) -> Vec<TermId> {
    match terms.get(term) {
        TermData::App(_, args) => args.to_vec(),
        other => panic!("expected an application, got {other:?}"),
    }
}

/// Lockstep: a plain (array-free) `Var` must map to ITSELF. Forgery: rename
/// the Int constant `y` to `x` in the abstract roots, turning `x = 1, y = 2`
/// into `x = 1, x = 2`.
#[test]
fn a_plain_constant_renamed_to_another_is_rejected() {
    const SCRIPT: &str = "\
        (declare-const u (Array Int (Array Int Int)))\
        (declare-const v (Array Int Int))\
        (declare-const x Int)\
        (declare-const y Int)\
        (assert (= (select u 0) v))\
        (assert (= x 1))\
        (assert (= y 2))";
    assert_honest_abstraction_is_uncertified(SCRIPT);

    let (mut exec, roots, abstraction) = built(SCRIPT);
    let (x, y) = (var_named(&exec, "x"), var_named(&exec, "y"));
    let mut map = ay_core::kani_compat::DetHashMap::default();
    map.insert(y, x);
    let forged_roots = abstraction
        .roots()
        .iter()
        .map(|&root| replace_term(&mut exec.ctx.terms, root, &map))
        .collect::<Vec<_>>();
    assert_ne!(forged_roots.as_slice(), abstraction.roots());
    let forged = ArrayUfAbstraction {
        roots: forged_roots.into_boxed_slice(),
        witness: abstraction.witness,
    };
    assert_certified_forgery_is_refused(&mut exec, &roots, forged);
}

/// Lockstep: a literal must map to ITSELF. Forgery: replace the literal `2`
/// by `1`, turning `x = 1, x != 2` into `x = 1, x != 1`.
#[test]
fn a_literal_replaced_by_another_is_rejected() {
    const SCRIPT: &str = "\
        (declare-const u (Array Int (Array Int Int)))\
        (declare-const v (Array Int Int))\
        (declare-const x Int)\
        (assert (= (select u 0) v))\
        (assert (= x 1))\
        (assert (not (= x 2)))";
    assert_honest_abstraction_is_uncertified(SCRIPT);

    let (mut exec, roots, abstraction) = built(SCRIPT);
    let one = exec.ctx.terms.mk_int(1.into());
    let two = exec.ctx.terms.mk_int(2.into());
    let mut map = ay_core::kani_compat::DetHashMap::default();
    map.insert(two, one);
    let forged_roots = abstraction
        .roots()
        .iter()
        .map(|&root| replace_term(&mut exec.ctx.terms, root, &map))
        .collect::<Vec<_>>();
    assert_ne!(forged_roots.as_slice(), abstraction.roots());
    let forged = ArrayUfAbstraction {
        roots: forged_roots.into_boxed_slice(),
        witness: abstraction.witness,
    };
    assert_certified_forgery_is_refused(&mut exec, &roots, forged);
}

/// Lockstep: a KEPT head must be the same symbol. Forgery: re-spell the kept
/// `=` of `(= x y)` as `distinct`, turning `x = 1, y = 1, x = y` into
/// `x = 1, y = 1, x != y`. Same arity, same sorts, same witness.
#[test]
fn a_kept_head_respelled_as_another_is_rejected() {
    const SCRIPT: &str = "\
        (declare-const u (Array Int (Array Int Int)))\
        (declare-const v (Array Int Int))\
        (declare-const x Int)\
        (declare-const y Int)\
        (assert (= (select u 0) v))\
        (assert (= x 1))\
        (assert (= y 1))\
        (assert (= x y))";
    assert_honest_abstraction_is_uncertified(SCRIPT);

    let (mut exec, roots, abstraction) = built(SCRIPT);
    let mut forged_roots = abstraction.roots().to_vec();
    let last = forged_roots.len() - 1;
    let args = app_args(&exec.ctx.terms, forged_roots[last]);
    forged_roots[last] = rebuild_app(
        &mut exec.ctx.terms,
        forged_roots[last],
        Symbol::named("distinct"),
        &args,
    );
    let forged = ArrayUfAbstraction {
        roots: forged_roots.into_boxed_slice(),
        witness: abstraction.witness,
    };
    assert_certified_forgery_is_refused(&mut exec, &roots, forged);
}

/// Lockstep: an application must keep its arity (`zip` alone would silently
/// ignore an extra argument). Forgery: append the conjunct `x = 2` to the
/// abstract image of `(and (= x 1) (= y 2))`.
#[test]
fn an_application_with_an_extra_argument_is_rejected() {
    let (mut exec, mut roots) = load(
        "(declare-const u (Array Int (Array Int Int)))\
         (declare-const v (Array Int Int))\
         (declare-const x Int)\
         (declare-const y Int)\
         (assert (= (select u 0) v))",
    );
    let (x, y) = (var_named(&exec, "x"), var_named(&exec, "y"));
    let terms = &mut exec.ctx.terms;
    let (one, two) = (terms.mk_int(1.into()), terms.mk_int(2.into()));
    let x_is_1 = terms.mk_app(Symbol::named("="), [x, one], Sort::Bool);
    let y_is_2 = terms.mk_app(Symbol::named("="), [y, two], Sort::Bool);
    let x_is_2 = terms.mk_app(Symbol::named("="), [x, two], Sort::Bool);
    roots.push(terms.mk_app(Symbol::named("and"), [x_is_1, y_is_2], Sort::Bool));
    let honest = ArrayUfAbstraction::build(terms, &roots).expect("the abstraction builds");
    assert!(
        is_pure_renaming(&exec.ctx.terms, &roots, &honest),
        "positive control"
    );
    assert!(
        exec.checked_strict_exact_unsat_solve(honest.roots().to_vec(), 5_000)
            .is_none(),
        "positive control: `x = 1 and y = 2` is satisfiable"
    );

    let mut forged_roots = honest.roots().to_vec();
    let last = forged_roots.len() - 1;
    let mut args = app_args(&exec.ctx.terms, forged_roots[last]);
    args.push(x_is_2);
    forged_roots[last] = rebuild_app(
        &mut exec.ctx.terms,
        forged_roots[last],
        Symbol::named("and"),
        &args,
    );
    let forged = ArrayUfAbstraction {
        roots: forged_roots.into_boxed_slice(),
        witness: honest.witness,
    };
    assert_certified_forgery_is_refused(&mut exec, &roots, forged);
}

/// The root vectors must have the same length (`zip` alone would silently
/// ignore an extra abstract root). Forgery: append `false` to the abstraction
/// of the satisfiable two-equality sibling.
#[test]
fn an_appended_abstract_root_is_rejected() {
    const SCRIPT: &str = "\
        (declare-const u (Array Int (Array Int Int)))\
        (declare-const v (Array Int Int))\
        (declare-const w (Array Int Int))\
        (assert (= (select u 0) v))\
        (assert (= (select u 0) w))";
    assert_honest_abstraction_is_uncertified(SCRIPT);

    let (mut exec, roots, abstraction) = built(SCRIPT);
    let mut forged_roots = abstraction.roots().to_vec();
    forged_roots.push(exec.ctx.terms.false_term());
    let forged = ArrayUfAbstraction {
        roots: forged_roots.into_boxed_slice(),
        witness: abstraction.witness,
    };
    assert_certified_forgery_is_refused(&mut exec, &roots, forged);
}

/// Lockstep: every image must have the sort `sigma(sort(original))`. Forgery:
/// re-sort the renamed `select`'s images from `Int` to `Bool`, turning three
/// pairwise distinct array reads into three pairwise distinct Booleans
/// (pigeonhole). Same heads, same arguments, same witness.
#[test]
fn an_image_at_a_changed_sort_is_rejected() {
    const SCRIPT: &str = "\
        (declare-const a (Array Int Int))\
        (assert (distinct (select a 0) (select a 1) (select a 2)))";
    assert_honest_abstraction_is_uncertified(SCRIPT);

    let (mut exec, roots, abstraction) = built(SCRIPT);
    let fresh_select = abstraction
        .witness
        .symbols
        .values()
        .next()
        .expect("one renamed select")
        .clone();
    let forged_roots = abstraction
        .roots()
        .iter()
        .map(|&root| resort_head(&mut exec.ctx.terms, root, &fresh_select, &Sort::Bool))
        .collect::<Vec<_>>();
    let forged = ArrayUfAbstraction {
        roots: forged_roots.into_boxed_slice(),
        witness: abstraction.witness,
    };
    assert_certified_forgery_is_refused(&mut exec, &roots, forged);
}

/// Rebuild `term` with every application of `head` given `sort`.
fn resort_head(terms: &mut TermStore, term: TermId, head: &Symbol, sort: &Sort) -> TermId {
    match terms.get(term).clone() {
        TermData::App(symbol, args) => {
            let args = args
                .iter()
                .map(|&arg| resort_head(terms, arg, head, sort))
                .collect::<Vec<_>>();
            let image_sort = if &symbol == head {
                sort.clone()
            } else {
                terms.sort(term).clone()
            };
            terms.mk_app(symbol, &args, image_sort)
        }
        TermData::Not(inner) => {
            let inner = resort_head(terms, inner, head, sort);
            terms.mk_not_raw(inner)
        }
        _ => term,
    }
}

/// Lockstep: a renamed constant must map to ITS witness image. Forgery: keep
/// the witness honest (so injectivity holds) and point only the ROOTS' `w`
/// at `v`'s image, turning `v != w` into `v' != v'`.
#[test]
fn a_renamed_constant_imaged_off_its_witness_is_rejected() {
    const SCRIPT: &str = "\
        (declare-const u (Array Int (Array Int Int)))\
        (declare-const v (Array Int Int))\
        (declare-const w (Array Int Int))\
        (assert (= (select u 0) v))\
        (assert (not (= v w)))";
    assert_honest_abstraction_is_uncertified(SCRIPT);

    let (mut exec, roots, abstraction) = built(SCRIPT);
    let (v, w) = (var_named(&exec, "v"), var_named(&exec, "w"));
    let mut map = ay_core::kani_compat::DetHashMap::default();
    map.insert(abstraction.witness.vars[&w], abstraction.witness.vars[&v]);
    let forged_roots = abstraction
        .roots()
        .iter()
        .map(|&root| replace_term(&mut exec.ctx.terms, root, &map))
        .collect::<Vec<_>>();
    assert_ne!(forged_roots.as_slice(), abstraction.roots());
    let forged = ArrayUfAbstraction {
        roots: forged_roots.into_boxed_slice(),
        witness: abstraction.witness,
    };
    assert_certified_forgery_is_refused(&mut exec, &roots, forged);
}

/// Lockstep: a head no rule classifies (here a user function over arrays,
/// which the builder declines) has no image at all. Forgery: abstract the
/// other roots honestly and image `(g v w)` as `(= v' w')`, which contradicts
/// the abstract `v' != w'`.
#[test]
fn an_unclassified_head_is_rejected() {
    let (mut exec, roots) = load(
        "(declare-fun g ((Array Int Int) (Array Int Int)) Bool)\
         (declare-const u (Array Int (Array Int Int)))\
         (declare-const v (Array Int Int))\
         (declare-const w (Array Int Int))\
         (assert (= (select u 0) v))\
         (assert (not (= v w)))\
         (assert (g v w))",
    );
    assert!(
        ArrayUfAbstraction::build(&mut exec.ctx.terms, &roots).is_none(),
        "the builder declines a user function over arrays"
    );
    let partial = ArrayUfAbstraction::build(&mut exec.ctx.terms, &roots[..2])
        .expect("the array-op-only roots abstract");
    assert!(
        exec.checked_strict_exact_unsat_solve(partial.roots().to_vec(), 5_000)
            .is_none(),
        "positive control: `v != w` alone is satisfiable"
    );
    let (v, w) = (var_named(&exec, "v"), var_named(&exec, "w"));
    let (v_image, w_image) = (partial.witness.vars[&v], partial.witness.vars[&w]);
    let mut forged_roots = partial.roots().to_vec();
    forged_roots.push(
        exec.ctx
            .terms
            .mk_app(Symbol::named("="), [v_image, w_image], Sort::Bool),
    );
    let forged = ArrayUfAbstraction {
        roots: forged_roots.into_boxed_slice(),
        witness: partial.witness,
    };
    assert_certified_forgery_is_refused(&mut exec, &roots, forged);
}

/// Lockstep: a quantifier's binder list must be unchanged. Forgery: re-bind
/// `(forall ((k Int)) (> x y))` as `(forall ((x Int)) (> x y))`, capturing
/// the free `x`; the body is the SAME term on both sides.
#[test]
fn a_quantifier_rebinding_a_free_variable_is_rejected() {
    let (mut exec, mut roots) = load(
        "(declare-const u (Array Int (Array Int Int)))\
         (declare-const v (Array Int Int))\
         (declare-const x Int)\
         (declare-const y Int)\
         (assert (= (select u 0) v))",
    );
    let (x, y) = (var_named(&exec, "x"), var_named(&exec, "y"));
    let body = exec
        .ctx
        .terms
        .mk_app(Symbol::named(">"), [x, y], Sort::Bool);
    roots.push(
        exec.ctx
            .terms
            .mk_forall(vec![("k".to_string(), Sort::Int)], body),
    );
    let honest =
        ArrayUfAbstraction::build(&mut exec.ctx.terms, &roots).expect("an Int binder builds");
    assert!(
        is_pure_renaming(&exec.ctx.terms, &roots, &honest),
        "positive control"
    );
    assert!(
        exec.checked_exact_unsat_solve(honest.roots().to_vec(), 5_000)
            .is_none(),
        "positive control: `forall k. x > y` is satisfiable"
    );

    let mut forged_roots = honest.roots().to_vec();
    let last = forged_roots.len() - 1;
    forged_roots[last] = exec
        .ctx
        .terms
        .mk_forall(vec![("x".to_string(), Sort::Int)], body);
    let forged = ArrayUfAbstraction {
        roots: forged_roots.into_boxed_slice(),
        witness: honest.witness,
    };
    assert_certified_forgery_is_refused(&mut exec, &roots, forged);
}

/// Witness: every fresh sort must be UNINTERPRETED. Forgery: map
/// `(Array Int Int)` to `Bool`, so three pairwise distinct arrays become three
/// pairwise distinct Booleans (pigeonhole).
#[test]
fn a_fresh_sort_that_is_interpreted_is_rejected() {
    const SCRIPT: &str = "\
        (declare-const a (Array Int Int))\
        (declare-const b (Array Int Int))\
        (declare-const c (Array Int Int))\
        (assert (distinct a b c))";
    assert_honest_abstraction_is_uncertified(SCRIPT);

    let (mut exec, roots) = load(SCRIPT);
    let mut witness = RenamingWitness::default();
    witness
        .sorts
        .insert(Sort::array(Sort::Int, Sort::Int), Sort::Bool);
    let mut map = ay_core::kani_compat::DetHashMap::default();
    for name in ["a", "b", "c"] {
        let original = var_named(&exec, name);
        let image = exec
            .ctx
            .terms
            .mk_var(format!("__ay_a2uf_c_forged_{name}"), Sort::Bool);
        witness.vars.insert(original, image);
        map.insert(original, image);
    }
    let forged_roots = roots
        .iter()
        .map(|&root| replace_term(&mut exec.ctx.terms, root, &map))
        .collect::<Vec<_>>();
    let forged = ArrayUfAbstraction {
        roots: forged_roots.into_boxed_slice(),
        witness,
    };
    assert_certified_forgery_is_refused(&mut exec, &roots, forged);
}

/// A "fresh" function must be one this rung minted, not merely a name the
/// original never applies: `=` or `distinct` in that role is interpreted by
/// the solver, and the induced structure `M'` cannot choose its meaning. No
/// strict certificate is known for these ill-typed forgeries today, so this
/// control pins the checker's contract rather than a reachable wrong answer.
#[test]
fn an_interpreted_symbol_posing_as_a_fresh_function_is_rejected() {
    const SCRIPT: &str = "\
        (declare-const a (Array Int Bool))\
        (assert (select a 0))";
    assert_honest_abstraction_is_uncertified(SCRIPT);
    for head in ["=", "distinct"] {
        let (mut exec, roots, mut abstraction) = built(SCRIPT);
        let (key, fresh) = abstraction
            .witness
            .symbols
            .iter()
            .next()
            .map(|(key, fresh)| (key.clone(), fresh.clone()))
            .expect("one renamed select");
        let interpreted = Symbol::named(head);
        abstraction.witness.symbols.insert(key, interpreted.clone());
        let forged_roots = abstraction
            .roots()
            .iter()
            .map(|&root| respell_head(&mut exec.ctx.terms, root, &fresh, &interpreted))
            .collect::<Vec<_>>();
        let forged = ArrayUfAbstraction {
            roots: forged_roots.into_boxed_slice(),
            witness: abstraction.witness,
        };
        assert!(
            !is_pure_renaming(&exec.ctx.terms, &roots, &forged),
            "`select` renamed to the interpreted `{head}`"
        );
    }
}
