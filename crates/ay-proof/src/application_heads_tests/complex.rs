// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn complex_reconstruction_heads_export_only_for_the_nominal_theory() {
    let mut terms = TermStore::new();
    let z = terms.mk_var("z", Sort::Complex);
    let real = terms.mk_complex_real(z).unwrap();
    let imaginary = terms.mk_complex_imaginary(z).unwrap();
    let rebuilt = terms.mk_complex(real, imaginary).unwrap();
    let eta = terms.mk_app(Symbol::named("="), [z, rebuilt], Sort::Bool);
    let premise = terms.mk_app(Symbol::named("="), [real, imaginary], Sort::Bool);
    let document =
        export_lemma(&terms, eta, &[premise], None).expect("nominal Complex heads resolve");
    assert!(document.contains("complex.make"));
    let mut proof = Proof::new();
    proof.add_theory_lemma("DT", vec![eta]);
    assert!(!crate::carcara_proof_surface_is_supported(
        &proof, &terms, None
    ));

    let mut owned = terms.clone();
    owned.register_declared_function("complex.make");
    assert_declines_naming(export_lemma(&owned, eta, &[premise], None), "complex.make");

    let fake = terms.mk_var("fake", Sort::Uninterpreted("Complex".into()));
    let forged = terms.mk_app(
        Symbol::named("complex.make"),
        [real, imaginary],
        terms.sort(fake).clone(),
    );
    let equality = terms.mk_app(Symbol::named("="), [fake, forged], Sort::Bool);
    let fake_premise = terms.mk_app(Symbol::named("="), [fake, fake], Sort::Bool);
    assert_declines_naming(
        export_lemma(&terms, equality, &[premise, fake_premise], None),
        "complex.make",
    );
}
