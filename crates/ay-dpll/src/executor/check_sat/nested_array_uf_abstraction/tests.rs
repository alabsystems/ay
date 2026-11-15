// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The renaming check and the linear token, each with the negative control
//! that shows it is not vacuous. The forgery controls, one per check that
//! stops the abstraction from being stronger than the original, live in the
//! `forgery` child, the declared-datatype carrier controls in `carrier`, and
//! the axiom-instance controls in `instance` (#nested-array-checked-rung).

use super::build::RenamingWitness;
use super::*;
use ay_core::{Sort, Symbol};

#[path = "carrier_tests.rs"]
mod carrier;
#[path = "forgery_tests.rs"]
mod forgery;
#[path = "instance_tests.rs"]
mod instance;

/// The congruence refutation the rung exists for: `(select u 0)` equals two
/// arrays asserted distinct.
const CONGRUENCE_UNSAT: &str = "\
    (declare-const u (Array Int (Array Int Int)))\
    (declare-const v (Array Int Int))\
    (declare-const w (Array Int Int))\
    (assert (= (select u 0) v))\
    (assert (= (select u 0) w))\
    (assert (not (= v w)))";

/// Load `script` (no check-sat) and return the executor and its hard roots.
fn load(script: &str) -> (Executor, Vec<TermId>) {
    let commands = ay_frontend::parse(script).expect("test input must parse");
    let mut exec = Executor::new();
    exec.execute_all(&commands)
        .expect("declarations and assertions execute");
    let roots = exec.ctx.assertions.clone();
    (exec, roots)
}

fn built(script: &str) -> (Executor, Vec<TermId>, ArrayUfAbstraction) {
    let (mut exec, roots) = load(script);
    let abstraction = ArrayUfAbstraction::build(&mut exec.ctx.terms, &roots)
        .expect("the abstraction builds for this shape");
    (exec, roots, abstraction)
}

fn var_named(exec: &Executor, name: &str) -> TermId {
    exec.ctx
        .terms
        .find_var(name)
        .expect("declared constant is interned")
}

#[test]
fn the_abstraction_of_the_congruence_refutation_is_an_array_free_pure_renaming() {
    let (exec, roots, abstraction) = built(CONGRUENCE_UNSAT);
    assert!(is_pure_renaming(&exec.ctx.terms, &roots, &abstraction));
    assert!(!StaticFeatures::collect(&exec.ctx.terms, abstraction.roots()).has_arrays);
    // Two array sorts, one typed `select`, three renamed constants.
    assert_eq!(abstraction.witness.sorts.len(), 2);
    assert_eq!(abstraction.witness.symbols.len(), 1);
    assert_eq!(abstraction.witness.vars.len(), 3);
}

#[test]
fn a_changed_root_vector_is_rejected() {
    let (exec, roots, abstraction) = built(CONGRUENCE_UNSAT);
    // Dropping a conjunct, witness intact, so only the length check sees it.
    // This is the harmless direction (fewer constraints); the dangerous one,
    // an APPENDED root, is `an_appended_abstract_root_is_rejected`.
    let dropped = ArrayUfAbstraction {
        roots: abstraction.roots[..2].into(),
        witness: RenamingWitness {
            sorts: abstraction.witness.sorts.clone(),
            symbols: abstraction.witness.symbols.clone(),
            vars: abstraction.witness.vars.clone(),
            swapped: abstraction.witness.swapped.clone(),
        },
    };
    assert!(!is_pure_renaming(&exec.ctx.terms, &roots, &dropped));
    // Replacing a conjunct by a STRONGER one (`false`) keeps the length and the
    // witness, and must still be rejected (here by the variant mismatch).
    let mut strengthened = abstraction.roots.to_vec();
    strengthened[2] = exec.ctx.terms.false_term();
    let strengthened = ArrayUfAbstraction {
        roots: strengthened.into_boxed_slice(),
        witness: abstraction.witness,
    };
    assert!(!is_pure_renaming(&exec.ctx.terms, &roots, &strengthened));
}

#[test]
fn collapsing_two_constants_onto_one_fresh_constant_is_rejected() {
    let (mut exec, roots, mut abstraction) = built(CONGRUENCE_UNSAT);
    let v = var_named(&exec, "v");
    let w = var_named(&exec, "w");
    let v_image = abstraction.witness.vars[&v];
    let w_image = abstraction.witness.vars[&w];
    // Point `w` at `v`'s image and rebuild the roots that mention `w`, so the
    // lockstep structure stays consistent and only injectivity is violated.
    abstraction.witness.vars.insert(w, v_image);
    let mut collapsed = Vec::new();
    for &root in abstraction.roots.iter() {
        let mut map = ay_core::kani_compat::DetHashMap::default();
        map.insert(w_image, v_image);
        collapsed.push(replace_term(&mut exec.ctx.terms, root, &map));
    }
    let collapsed = ArrayUfAbstraction {
        roots: collapsed.into_boxed_slice(),
        witness: abstraction.witness,
    };
    assert!(!is_pure_renaming(&exec.ctx.terms, &roots, &collapsed));
}

/// Rebuild `term` with every occurrence of a key of `map` replaced, using the
/// same raw constructors as the builder.
fn replace_term(
    terms: &mut TermStore,
    term: TermId,
    map: &ay_core::kani_compat::DetHashMap<TermId, TermId>,
) -> TermId {
    if let Some(&to) = map.get(&term) {
        return to;
    }
    match terms.get(term).clone() {
        TermData::App(symbol, args) => {
            let args = args
                .iter()
                .map(|&arg| replace_term(terms, arg, map))
                .collect::<Vec<_>>();
            let sort = terms.sort(term).clone();
            terms.mk_app(symbol, &args, sort)
        }
        TermData::Not(inner) => {
            let inner = replace_term(terms, inner, map);
            terms.mk_not_raw(inner)
        }
        _ => term,
    }
}

#[test]
fn keeping_an_array_operation_at_an_abstract_sort_is_rejected() {
    let (mut exec, roots, abstraction) = built(CONGRUENCE_UNSAT);
    // Re-spell the renamed `select` as the ORIGINAL `select` over the abstract
    // sorts: same shape, same witness, but a kept head at a changed signature.
    let fresh_select = abstraction
        .witness
        .symbols
        .values()
        .next()
        .expect("one renamed select")
        .clone();
    let mut respelled = Vec::new();
    for &root in abstraction.roots.iter() {
        respelled.push(respell_head(
            &mut exec.ctx.terms,
            root,
            &fresh_select,
            &Symbol::named("select"),
        ));
    }
    assert_ne!(respelled.as_slice(), abstraction.roots());
    let respelled = ArrayUfAbstraction {
        roots: respelled.into_boxed_slice(),
        witness: abstraction.witness,
    };
    assert!(!is_pure_renaming(&exec.ctx.terms, &roots, &respelled));
}

fn respell_head(terms: &mut TermStore, term: TermId, from: &Symbol, to: &Symbol) -> TermId {
    match terms.get(term).clone() {
        TermData::App(symbol, args) => {
            let args = args
                .iter()
                .map(|&arg| respell_head(terms, arg, from, to))
                .collect::<Vec<_>>();
            let sort = terms.sort(term).clone();
            let head = if &symbol == from { to.clone() } else { symbol };
            terms.mk_app(head, &args, sort)
        }
        TermData::Not(inner) => {
            let inner = respell_head(terms, inner, from, to);
            terms.mk_not_raw(inner)
        }
        _ => term,
    }
}

#[test]
fn a_fresh_identity_that_occurs_in_the_original_is_rejected() {
    // `h` is an ORIGINAL symbol (kept at `Int -> Int`) that happens to carry
    // the rung's own mint spelling, so the mint test cannot reject it (an
    // original built internally, e.g. from an earlier abstraction's output, can
    // contain such a name). Re-spell the renamed `select` as `h` consistently
    // in the witness AND the abstract roots: the lockstep structure still
    // matches, so only freshness can reject it. The induced structure would
    // need `h` to be both the original's function and `select`.
    fn load_with_h() -> (Executor, Vec<TermId>, Symbol) {
        let (mut exec, mut roots) = load(
            "(declare-const u (Array Int (Array Int Int)))\
             (declare-const v (Array Int Int))\
             (assert (= (select u 0) v))",
        );
        let h = Symbol::named("__ay_a2uf_fn!999999");
        let terms = &mut exec.ctx.terms;
        let (zero, one) = (terms.mk_int(0.into()), terms.mk_int(1.into()));
        let h_one = terms.mk_app(h.clone(), [one], Sort::Int);
        roots.push(terms.mk_app(Symbol::named(">"), [h_one, zero], Sort::Bool));
        (exec, roots, h)
    }
    let (mut exec, roots, _) = load_with_h();
    let abstraction =
        ArrayUfAbstraction::build(&mut exec.ctx.terms, &roots).expect("the abstraction builds");
    assert!(
        is_pure_renaming(&exec.ctx.terms, &roots, &abstraction),
        "positive control"
    );

    let (mut exec, roots, h) = load_with_h();
    let mut abstraction =
        ArrayUfAbstraction::build(&mut exec.ctx.terms, &roots).expect("the abstraction builds");
    let (key, fresh_select) = abstraction
        .witness
        .symbols
        .iter()
        .next()
        .map(|(key, fresh)| (key.clone(), fresh.clone()))
        .expect("one renamed select");
    abstraction.witness.symbols.insert(key, h.clone());
    let mut respelled = Vec::new();
    for &root in abstraction.roots.iter() {
        respelled.push(respell_head(&mut exec.ctx.terms, root, &fresh_select, &h));
    }
    let collided = ArrayUfAbstraction {
        roots: respelled.into_boxed_slice(),
        witness: abstraction.witness,
    };
    assert!(!is_pure_renaming(&exec.ctx.terms, &roots, &collided));
}

#[test]
fn an_original_constant_posing_as_a_fresh_image_is_rejected() {
    let (exec, roots, mut abstraction) = built(CONGRUENCE_UNSAT);
    // Claim that the ORIGINAL constant `v` is the "fresh" image of `w`.
    let v = var_named(&exec, "v");
    let w = var_named(&exec, "w");
    abstraction.witness.vars.insert(w, v);
    assert!(!is_pure_renaming(&exec.ctx.terms, &roots, &abstraction));
}

#[test]
fn a_quantifier_binding_an_array_sort_declines_to_build() {
    let (mut exec, roots) = load(
        "(declare-const u (Array Int (Array Int Int)))\
         (assert (forall ((a (Array Int Int))) (not (= (select u 0) a))))",
    );
    assert!(ArrayUfAbstraction::build(&mut exec.ctx.terms, &roots).is_none());
}

#[test]
fn a_lambda_array_declines_to_build() {
    let (mut exec, _) = load("(declare-const u (Array Int (Array Int Int)))");
    let u = var_named(&exec, "u");
    let terms = &mut exec.ctx.terms;
    let x = terms.mk_var("x", Sort::Int);
    let zero = terms.mk_int(0.into());
    let lambda = terms.mk_lambda_array(x, x);
    let read = terms.mk_app(
        Symbol::named("select"),
        [u, zero],
        Sort::array(Sort::Int, Sort::Int),
    );
    let root = terms.mk_app(Symbol::named("="), [read, lambda], Sort::Bool);
    assert!(ArrayUfAbstraction::build(terms, &[root]).is_none());
}

#[test]
fn an_array_constant_whose_name_a_binder_reuses_is_rejected() {
    // The frontend alpha-renames a binder that shadows a declaration (`x` is
    // bound as `x_2` when parsed), so build the collision directly: a
    // quantifier binding `x : Int` beside the array constant `x`. The checker
    // must not rely on the frontend's hygiene.
    let (mut exec, mut roots) = load(
        "(declare-const x (Array Int (Array Int Int)))\
         (declare-const v (Array Int Int))\
         (assert (= (select x 0) v))",
    );
    let terms = &mut exec.ctx.terms;
    let bound = terms.mk_var("x", Sort::Int);
    let zero = terms.mk_int(0.into());
    let body = terms.mk_app(Symbol::named(">="), [bound, zero], Sort::Bool);
    roots.push(terms.mk_forall(vec![("x".to_string(), Sort::Int)], body));
    let abstraction = ArrayUfAbstraction::build(terms, &roots).expect("an Int binder builds");
    assert!(!is_pure_renaming(&exec.ctx.terms, &roots, &abstraction));

    // Positive control: the same shape with an unrelated binder name.
    let (mut exec, mut roots) = load(
        "(declare-const x (Array Int (Array Int Int)))\
         (declare-const v (Array Int Int))\
         (assert (= (select x 0) v))",
    );
    let terms = &mut exec.ctx.terms;
    let bound = terms.mk_var("k", Sort::Int);
    let zero = terms.mk_int(0.into());
    let body = terms.mk_app(Symbol::named(">="), [bound, zero], Sort::Bool);
    roots.push(terms.mk_forall(vec![("k".to_string(), Sort::Int)], body));
    let abstraction = ArrayUfAbstraction::build(terms, &roots).expect("an Int binder builds");
    assert!(is_pure_renaming(&exec.ctx.terms, &roots, &abstraction));
}

fn has_quantified_root(exec: &Executor, roots: &[TermId]) -> bool {
    roots.iter().any(|&root| exec.ctx.terms.is_quantifier(root))
}

/// A parsed quantified problem is in scope as long as no binder has an array
/// sort: the array-free binder and its body survive unchanged.
#[test]
fn a_parsed_quantifier_over_an_array_free_binder_is_accepted() {
    let (exec, roots, abstraction) = built(
        "(declare-fun f (Int) Int)\
         (declare-const x (Array Int (Array Int Int)))\
         (declare-const v (Array Int Int))\
         (assert (= (select x 0) v))\
         (assert (forall ((k Int)) (> (f k) 0)))",
    );
    assert!(has_quantified_root(&exec, &roots));
    assert!(is_pure_renaming(&exec.ctx.terms, &roots, &abstraction));
}

fn checked_token(exec: &mut Executor, abstraction: &ArrayUfAbstraction) -> CheckedExactUnsat {
    exec.checked_strict_exact_unsat_solve(abstraction.roots().to_vec(), 5_000)
        .expect("the pure-EUF abstraction certifies UNSAT on a strict proof")
}

#[test]
fn the_token_consumes_only_for_the_exact_roots_it_was_built_from() {
    let (mut exec, roots, abstraction) = built(CONGRUENCE_UNSAT);
    let checked = checked_token(&mut exec, &abstraction);
    let token = CheckedArrayUfAbstractionUnsat {
        checked,
        original: roots.clone().into_boxed_slice(),
        abstraction,
        instances: Box::default(),
    };
    let mut reordered = roots.clone();
    reordered.swap(0, 1);
    assert!(!token.consume(&mut exec, &reordered));

    let (mut exec, roots, abstraction) = built(CONGRUENCE_UNSAT);
    let checked = checked_token(&mut exec, &abstraction);
    let token = CheckedArrayUfAbstractionUnsat {
        checked,
        original: roots.clone().into_boxed_slice(),
        abstraction,
        instances: Box::default(),
    };
    assert!(token.consume(&mut exec, &roots), "positive control");
}

#[test]
fn the_token_is_refused_once_the_term_store_moves() {
    let (mut exec, roots, abstraction) = built(CONGRUENCE_UNSAT);
    let checked = checked_token(&mut exec, &abstraction);
    let _later = exec.ctx.terms.mk_var("__ay_test_later", Sort::Int);
    let token = CheckedArrayUfAbstractionUnsat {
        checked,
        original: roots.clone().into_boxed_slice(),
        abstraction,
        instances: Box::default(),
    };
    assert!(!token.consume(&mut exec, &roots));
}

#[test]
fn a_current_certificate_does_not_launder_a_broken_witness() {
    let (mut exec, roots, abstraction) = built(CONGRUENCE_UNSAT);
    let checked = checked_token(&mut exec, &abstraction);
    // Same certified abstract roots, witness emptied: the certificate is
    // current, but nothing ties the abstract problem to `roots` any more.
    let token = CheckedArrayUfAbstractionUnsat {
        checked,
        original: roots.clone().into_boxed_slice(),
        abstraction: ArrayUfAbstraction {
            roots: abstraction.roots,
            witness: RenamingWitness::default(),
        },
        instances: Box::default(),
    };
    assert!(!token.consume(&mut exec, &roots));
}

#[test]
fn a_satisfiable_abstraction_yields_no_certificate() {
    // Drop the disequality: the abstraction is satisfiable, so no checked
    // UNSAT authority can exist for it.
    let (mut exec, _, abstraction) = built(
        "(declare-const u (Array Int (Array Int Int)))\
         (declare-const v (Array Int Int))\
         (declare-const w (Array Int Int))\
         (assert (= (select u 0) v))\
         (assert (= (select u 0) w))",
    );
    assert!(exec
        .checked_strict_exact_unsat_solve(abstraction.roots().to_vec(), 5_000)
        .is_none());
}

/// The certificate-class negative control. The quantified Ultimate Automizer
/// repro's abstraction IS refuted (z3 agrees), but the probe can back that
/// refutation only by an independent re-solve (`DischargedTrust`), never by a
/// strict proof. The strict mode must refuse it, and the rung with it, while
/// the broader exact-UNSAT mode accepts the same roots: the narrowing is
/// what keeps this verdict withheld.
///
/// If a future proof-reconstruction change makes the strict leg accept, this
/// test fails on purpose: that is the moment to re-measure and update the
/// quantified pin in `executor_tests::array_soundness`.
#[test]
fn a_refutation_without_a_strict_proof_is_refused() {
    let script =
        include_str!("../../../../../../repros/abv-nested-array-quantified-unsat-quarantine.smt2")
            .replace("(check-sat)", "")
            .replace("(exit)", "");
    let (mut exec, roots, abstraction) = built(&script);
    assert!(is_pure_renaming(&exec.ctx.terms, &roots, &abstraction));
    assert!(
        exec.checked_strict_exact_unsat_solve(abstraction.roots().to_vec(), 5_000)
            .is_none(),
        "no strict proof exists for this abstraction today"
    );
    assert!(!exec.nested_array_uf_abstraction_unsat(&roots));

    let (mut exec, _, abstraction) = built(&script);
    assert!(
        exec.checked_exact_unsat_solve(abstraction.roots().to_vec(), 5_000)
            .is_some(),
        "positive control: the broader exact-UNSAT mode accepts the same roots"
    );
}

#[test]
fn the_rung_declines_when_a_proof_artifact_is_requested() {
    let (mut exec, roots) = load(CONGRUENCE_UNSAT);
    exec.set_produce_proofs(true);
    assert!(!exec.nested_array_uf_abstraction_unsat(&roots));
}

#[test]
fn the_rung_stands_down_after_its_failure_allowance() {
    let (mut exec, roots) = load(CONGRUENCE_UNSAT);
    exec.array_uf_abstraction_failures = ABSTRACTION_MAX_FAILURES;
    assert!(!exec.nested_array_uf_abstraction_unsat(&roots));
    exec.array_uf_abstraction_failures = 0;
    assert!(
        exec.nested_array_uf_abstraction_unsat(&roots),
        "positive control"
    );
}
