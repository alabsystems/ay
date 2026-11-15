// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Lemma-plan shapes over hand-built instance logs. The end-to-end
//! certificate (real search, probe, stitch, strict boundary) is covered by
//! `executor_tests/quantifier/qlra/m3_unsat_cert.rs`.

use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::term::TermData;
use ay_core::{Sort, TermId, TermStore};

use super::lemma_plan::{build_lemma_plan, LemmaKind, PlanDecline};
use crate::cegqi::lra_nested::approx::NInstance;
use crate::cegqi::lra_nested::ntree::build_nested_tree;

fn binder(name: &str) -> Vec<(String, Sort)> {
    vec![(name.to_string(), Sort::Real)]
}

fn instance(terms: &mut TermStore, tuple: Vec<TermId>) -> NInstance {
    NInstance {
        tuple,
        frozen: terms.mk_bool(true),
        round: 0,
    }
}

/// Whether `term` mentions any of `needles`.
fn mentions(terms: &TermStore, term: TermId, needles: &HashSet<TermId>) -> bool {
    let mut stack = vec![term];
    let mut seen = HashSet::default();
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        if needles.contains(&t) {
            return true;
        }
        match terms.get(t) {
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(c, a, b) => stack.extend([*c, *a, *b]),
            TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => stack.push(*body),
            _ => {}
        }
    }
    false
}

/// `∃y ∀x. y > x` with Γ = {x ↦ sk_y}: one `sko` lemma for the authored
/// existential and one `forall_inst` lemma whose value is the REGISTERED
/// witness, never the search's own Skolem constant.
#[test]
fn p2_plan_is_one_skolem_and_one_instance_over_the_registered_witness() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let gt = terms.mk_gt(y, x);
    let inner = terms.mk_forall(binder("x"), gt);
    let root = terms.mk_exists(binder("y"), inner);
    let tree = build_nested_tree(&mut terms, &[root]).expect("tree");
    let search_skolem = tree.skolems[0];
    let gamma = vec![vec![instance(&mut terms, vec![search_skolem])]];
    let plan = build_lemma_plan(&mut terms, &tree, &gamma, &[root]).expect("plan");
    assert_eq!(plan.lemmas.len(), 2, "{:?}", plan.lemmas);
    let LemmaKind::Skolem {
        quantified,
        witness,
    } = plan.lemmas[0].kind.clone()
    else {
        panic!("first lemma must be the Skolem step: {:?}", plan.lemmas[0]);
    };
    assert_eq!(quantified, root);
    assert!(
        terms.skolem_choice(witness).is_some(),
        "the witness is registered"
    );
    let LemmaKind::ForallInst { quantifier, values } = plan.lemmas[1].kind.clone() else {
        panic!("second lemma must be forall_inst: {:?}", plan.lemmas[1]);
    };
    assert_eq!(
        values,
        vec![witness],
        "the tuple is transported onto the witness"
    );
    // The instantiated universal is the authored inner forall over the witness.
    assert!(matches!(terms.get(quantifier), TermData::Forall(..)));
    let search_constants: HashSet<TermId> = tree
        .skolems
        .iter()
        .copied()
        .chain(tree.nodes.iter().flat_map(|n| n.ce_vars.iter().copied()))
        .collect();
    for lemma in &plan.lemmas {
        assert!(
            !mentions(&terms, lemma.term, &search_constants),
            "a lemma leaked a search constant: {lemma:?}"
        );
    }
}

/// A logged tuple that names a search constant with no surface counterpart
/// (the node's OWN counterexample constant) declines.
#[test]
fn a_tuple_over_an_unaligned_search_constant_declines() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let gt = terms.mk_gt(y, x);
    let inner = terms.mk_forall(binder("x"), gt);
    let root = terms.mk_exists(binder("y"), inner);
    let tree = build_nested_tree(&mut terms, &[root]).expect("tree");
    let own = tree.nodes[0].ce_vars[0];
    let gamma = vec![vec![instance(&mut terms, vec![own])]];
    assert_eq!(
        build_lemma_plan(&mut terms, &tree, &gamma, &[root]).unwrap_err(),
        PlanDecline::Unbound
    );
}

/// A two-binder effective existential would need a multi-binder `sko`.
#[test]
fn a_multi_binder_effective_existential_declines() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Real);
    let b = terms.mk_var("b", Sort::Real);
    let x = terms.mk_var("x", Sort::Real);
    let sum = terms.mk_add(vec![a, b]);
    let gt = terms.mk_gt(sum, x);
    let inner = terms.mk_forall(binder("x"), gt);
    let root = terms.mk_exists(
        vec![("a".to_string(), Sort::Real), ("b".to_string(), Sort::Real)],
        inner,
    );
    let tree = build_nested_tree(&mut terms, &[root]).expect("tree");
    let gamma = vec![Vec::new(); tree.nodes.len()];
    assert_eq!(
        build_lemma_plan(&mut terms, &tree, &gamma, &[root]).unwrap_err(),
        PlanDecline::MultiBinderSkolem
    );
}

/// Roots that are not the ones the tree was built from do not align.
#[test]
fn foreign_roots_decline() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let zero = terms.mk_rational(num_rational::BigRational::from_integer(0.into()));
    let gt = terms.mk_gt(x, zero);
    let root = terms.mk_forall(binder("x"), gt);
    let tree = build_nested_tree(&mut terms, &[root]).expect("tree");
    let gamma = vec![Vec::new(); tree.nodes.len()];
    assert_eq!(
        build_lemma_plan(&mut terms, &tree, &gamma, &[root, root]).unwrap_err(),
        PlanDecline::Alignment
    );
    let lt = terms.mk_lt(x, zero);
    let other = terms.mk_forall(binder("x"), lt);
    assert!(build_lemma_plan(&mut terms, &tree, &gamma, &[other]).is_err());
}
