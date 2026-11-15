// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The certificate's proxy renaming and its ground probe.
//!
//! Measured while building M3a: an instance body whose arithmetic cancels to
//! a constant (`60 = -21` once the search's value replaces its binder) was
//! FOLDED by the probe's preprocessing, the rewritten assertion demoted to a
//! premiseless `trust`, and the probe's own strict check refused a correct
//! refutation (RND_3_5). Constant atoms are therefore proxied with unit
//! facts, and the probe skips sum-of-monomials normalization.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::TermData;
use ay_core::{Sort, TermId};
use ay_frontend::parse;

use super::super::proxy_renaming::{constant_atom_value, ProxyRenaming};
use crate::executor::quantifier_loop::result_mapping::{
    SameContextProbeOutcome, SameContextWindow,
};
use crate::Executor;

/// `(forall y. (or (not p) (= (+ (* y 81) (* sk -23)) -21)))`, `p`, and the
/// value `sk·23/81 + 20/27` that makes the atom the constant `60 = -21`.
const FOLDING: &str =
    "(set-logic LRA)(declare-const p Bool)(declare-const sk Real)(declare-const d Real)
(assert (forall ((y Real)) (or (not p) (= (+ (* y 81.0) (* sk (- 23.0))) (- 21.0)))))
(assert (= d (+ (* sk (/ 23.0 81.0)) (/ 20.0 27.0))))
(assert p)";

/// The raw instance `(or (not p) (= (+ (* v 81) (* sk -23)) -21))` (exact
/// substitution, no folding) and `p`.
fn folding_instance(exec: &mut Executor) -> (TermId, TermId) {
    let commands = parse(FOLDING).expect("parse");
    exec.execute_all(&commands).expect("execute");
    let a = exec.ctx.assertions.clone();
    let TermData::Forall(binders, body, _) = exec.ctx.terms.get(a[0]).clone() else {
        panic!("forall");
    };
    let TermData::App(_, args) = exec.ctx.terms.get(a[1]).clone() else {
        panic!("definition");
    };
    let map: HashMap<String, TermId> = [(binders[0].0.clone(), args[1])].into_iter().collect();
    let instance = crate::ematching::subst_vars_exact_qf(&mut exec.ctx.terms, body, &map)
        .expect("substitution");
    (instance, a[2])
}

fn constant_atom(exec: &Executor, instance: TermId) -> TermId {
    let TermData::App(_, disjuncts) = exec.ctx.terms.get(instance).clone() else {
        panic!("or");
    };
    disjuncts[1]
}

#[test]
fn a_variable_free_comparison_is_a_constant_atom_with_its_value() {
    let mut exec = Executor::new();
    let (instance, _) = folding_instance(&mut exec);
    let atom = constant_atom(&exec, instance);
    assert_eq!(
        constant_atom_value(&exec.ctx.terms, atom),
        Some(false),
        "60 = -21"
    );
    let x = exec.ctx.terms.mk_var("x", Sort::Real);
    let one = exec
        .ctx
        .terms
        .mk_rational(num_rational::BigRational::from_integer(1.into()));
    let open = exec
        .ctx
        .terms
        .mk_app(ay_core::Symbol::named("<"), vec![x, one], Sort::Bool);
    assert_eq!(
        constant_atom_value(&exec.ctx.terms, open),
        None,
        "x < 1 is no constant"
    );
}

#[test]
fn a_constant_atom_is_proxied_and_round_trips_with_a_unit_fact() {
    let mut exec = Executor::new();
    let (instance, _) = folding_instance(&mut exec);
    let atom = constant_atom(&exec, instance);
    let mut renaming = ProxyRenaming::default();
    let proxied = renaming
        .proxy(&mut exec.ctx.terms, instance)
        .expect("proxy");
    assert_ne!(proxied, instance);
    assert_eq!(
        renaming.rename(&mut exec.ctx.terms, proxied),
        Some(instance)
    );
    let [(proxy, constant, truth)] = renaming.constants() else {
        panic!("one constant atom: {:?}", renaming.constants());
    };
    let (proxy, constant, truth) = (*proxy, *constant, *truth);
    assert_eq!((constant, truth), (atom, false));
    let facts = renaming.constant_facts(&mut exec.ctx.terms);
    let negated = exec.ctx.terms.mk_not_raw(proxy);
    assert_eq!(facts, vec![negated]);
}

/// The raw folding instance defeats the probe (its strict check meets a
/// premiseless `trust`); its proxied form plus the unit fact refutes with a
/// strict-complete proof.
#[test]
fn the_probe_certifies_the_proxied_folding_instance() {
    let mut exec = Executor::new();
    let (instance, p) = folding_instance(&mut exec);
    let raw = exec.checked_same_context_unsat_proof(
        &[instance, p],
        SameContextWindow::Ground,
        Some(5_000),
        None,
        true,
    );
    assert!(
        matches!(raw, SameContextProbeOutcome::UnsatUnpromotable),
        "the raw instance folds in preprocessing (if it now certifies, the proxying is not needed)"
    );
    let mut renaming = ProxyRenaming::default();
    let proxied = renaming
        .proxy(&mut exec.ctx.terms, instance)
        .expect("proxy");
    let mut set = vec![proxied, p];
    set.extend(renaming.constant_facts(&mut exec.ctx.terms));
    let outcome = exec.checked_same_context_unsat_proof(
        &set,
        SameContextWindow::Ground,
        Some(5_000),
        None,
        true,
    );
    assert!(matches!(outcome, SameContextProbeOutcome::Proof(_)));
}
