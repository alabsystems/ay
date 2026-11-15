// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::kani_compat::DetHashMap;
use ay_core::{Proof, Sort, Symbol, TheoryLemmaKind};

fn fixture(writes: usize, value_depth: usize) -> (TermStore, TermId, TermId) {
    let mut terms = TermStore::new();
    let sort = Sort::array(Sort::Int, Sort::Int);
    let a = terms.mk_var("a", sort.clone());
    let k = terms.mk_var("k", Sort::Int);
    let u = terms.mk_var("u", Sort::Int);
    let v = terms.mk_var("v", Sort::Int);
    let mut old = u;
    for _ in 0..value_depth {
        old = terms.mk_app(Symbol::named("f"), [old], Sort::Int);
    }
    let mut left = a;
    for n in 0..writes {
        let value = if n + 1 == writes {
            v
        } else if n == 0 {
            old
        } else {
            u
        };
        left = terms.mk_app(Symbol::named("store"), [left, k, value], sort.clone());
    }
    let right = terms.mk_app(Symbol::named("store"), [a, k, v], sort);
    let eq = terms.mk_app(Symbol::named("="), [left, right], Sort::Bool);
    let root = terms.mk_not_raw(eq);
    (terms, root, eq)
}

#[test]
fn shadowed_assume_identity_preserves_scoped_publication() {
    let (terms, root, eq) = fixture(80, 0);
    let surface = crate::render_term_canonical(&terms, root);
    assert_eq!(
        exact_input_bytes(&terms, root, &surface),
        Some(2 * surface.len())
    );
    let mut proof = Proof::new();
    let assumed = proof.add_assume(root, None);
    let lemma = proof.add_theory_lemma_with_kind("array", vec![eq], TheoryLemmaKind::ArrayRowChain);
    proof.add_resolution(vec![], eq, lemma, assumed);
    crate::check_proof_strict(&proof, &terms).unwrap();
    let mut overrides = DetHashMap::default();
    overrides.insert(root, surface.clone());
    let document = crate::try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &[root],
        Some(&overrides),
    )
    .expect("an exact canonical spelling needs no equivalence bridge");
    assert!(document.contains(":rule arrays_ext") && !document.contains(":rule hole"));
    let problem = format!("(set-logic QF_AUFLIA)\n(declare-fun a () (Array Int Int))\n(declare-fun k () Int)\n(declare-fun u () Int)\n(declare-fun v () Int)\n(assert {surface})\n(check-sat)\n");
    let path = std::env::temp_dir().join(format!(
        "ay-shadow-authored-identity-{}.json",
        std::process::id()
    ));
    std::fs::write(&path, serde_json::to_vec(&serde_json::json!({"type":"alethe_certificate","version":"1.0","problem":problem,"proof":document})).unwrap()).unwrap();
    println!("independent replay certificate: {}", path.display());

    overrides.insert(root, "false".into());
    let error = crate::try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &[root],
        Some(&overrides),
    )
    .expect_err("a changed source rendering cannot use the identity path");
    assert!(error.to_string().contains("structural rendering bound"));
}

#[test]
fn shadowed_assume_identity_retains_shape_depth_and_payload_bounds() {
    for (writes, depth) in [(129, 0), (80, 140)] {
        let (terms, root, _) = fixture(writes, depth);
        let surface = crate::render_term_canonical(&terms, root);
        assert_eq!(exact_input_bytes(&terms, root, &surface), None);
    }
    let (terms, root, eq) = fixture(80, 0);
    let canonical = crate::render_term_canonical(&terms, root);
    assert_eq!(exact_input_bytes(&terms, eq, &canonical), None);
    assert_eq!(
        exact_input_bytes(&terms, root, &"x".repeat(MAX_EQUIVALENCE_BYTES + 1)),
        None
    );
    assert_eq!(
        exact_input_bytes(&terms, root, &canonical.replace(" v)", " u)")),
        None
    );
}
