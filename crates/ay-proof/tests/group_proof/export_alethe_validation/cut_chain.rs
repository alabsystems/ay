// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// The Chvátal–Gomory cut-chain lemma (`IntCgCutChain`) against the pinned
// external checker. The fixture is the thirteen rows the refutation of
// `QF_LIA_ring_2exp16_5vars_cascade_unsat` uses, as authored assertions: the
// negation of the lemma is rationally satisfiable (`Σ m_i = 262145/3`), so
// only integer rounding refutes it. AY's strict checker validates the chain,
// and the exported document must be Carcara `valid` with no allowance — one
// `la_generic` per cut, not a `hole`.

const QF_LIA_CASCADE_CUT_CHAIN_UNSAT: &str = r#"
(set-logic QF_LIA)
(declare-const s1 Int)
(declare-const s2 Int)
(declare-const s3 Int)
(declare-const c1 Int)
(declare-const c2 Int)
(declare-const c3 Int)
(declare-const c4 Int)
(declare-const m1 Int)
(declare-const m2 Int)
(declare-const m3 Int)
(declare-const m4 Int)
(declare-const m5 Int)
(assert (= (+ s3 (* 3 m5)) (+ (* 65536 c4) 1)))
(assert (= (+ (* 65536 c3) s3) (+ s2 (* 3 m4))))
(assert (= (+ (* 65536 c1) s1) (+ (* 3 m1) (* 3 m2))))
(assert (= (+ (* 65536 c2) s2) (+ s1 (* 3 m3))))
(assert (<= 40000 (* 3 m1)))
(assert (<= 40000 (* 3 m2)))
(assert (<= 40000 (* 3 m3)))
(assert (<= 40000 (* 3 m4)))
(assert (<= 40000 (* 3 m5)))
(assert (<= c1 1))
(assert (<= c2 1))
(assert (<= c3 1))
(assert (<= c4 1))
(check-sat)
"#;

/// The fixture's thirteen roots, spelled exactly as the problem writes them.
fn cascade_roots(terms: &mut TermStore) -> Vec<TermId> {
    let var = |terms: &mut TermStore, name: &str| terms.mk_var(name, Sort::Int);
    let s: Vec<TermId> = ["s1", "s2", "s3"].iter().map(|n| var(terms, n)).collect();
    let c: Vec<TermId> = ["c1", "c2", "c3", "c4"]
        .iter()
        .map(|n| var(terms, n))
        .collect();
    let m: Vec<TermId> = ["m1", "m2", "m3", "m4", "m5"]
        .iter()
        .map(|n| var(terms, n))
        .collect();
    let (three, word) = (lattice_int(terms, 3), lattice_int(terms, 65536));
    let m3: Vec<TermId> = m
        .iter()
        .map(|&mi| lattice_app(terms, "*", &[three, mi]))
        .collect();
    let c16: Vec<TermId> = c
        .iter()
        .map(|&ci| lattice_app(terms, "*", &[word, ci]))
        .collect();
    let one = lattice_int(terms, 1);
    let mut roots = Vec::new();
    for (lhs, rhs) in [
        ([s[2], m3[4]], [c16[3], one]),
        ([c16[2], s[2]], [s[1], m3[3]]),
        ([c16[0], s[0]], [m3[0], m3[1]]),
        ([c16[1], s[1]], [s[0], m3[2]]),
    ] {
        let lhs = lattice_app(terms, "+", &lhs);
        let rhs = lattice_app(terms, "+", &rhs);
        roots.push(lattice_app(terms, "=", &[lhs, rhs]));
    }
    let low = lattice_int(terms, 40000);
    for &mi3 in &m3 {
        roots.push(terms.mk_app(ay_core::Symbol::named("<="), [low, mi3], Sort::Bool));
    }
    for &ci in &c {
        roots.push(terms.mk_app(ay_core::Symbol::named("<="), [ci, one], Sort::Bool));
    }
    roots
}

/// Assume every root, state the cut-chain lemma over their negations, and
/// resolve it away root by root.
fn cut_chain_refutation(terms: &mut TermStore, roots: &[TermId]) -> Proof {
    let mut proof = Proof::new();
    let assumes: Vec<_> = roots
        .iter()
        .map(|&root| proof.add_assume(root, None))
        .collect();
    let negated: Vec<TermId> = roots.iter().map(|&root| terms.mk_not_raw(root)).collect();
    let mut current =
        proof.add_theory_lemma_with_kind("LIA", negated.clone(), TheoryLemmaKind::IntCgCutChain);
    for (index, (&root, &assume)) in roots.iter().zip(&assumes).enumerate() {
        current = proof.add_resolution(negated[index + 1..].to_vec(), root, assume, current);
    }
    proof
}

#[test]
fn exports_a_cut_chain_lemma_that_carcara_accepts() {
    let mut terms = TermStore::new();
    let roots = cascade_roots(&mut terms);
    let proof = cut_chain_refutation(&mut terms, &roots);
    check_proof_strict(&proof, &terms).expect("the cut chain is strictly certified");
    let alethe = export_alethe_with_problem_scope(&proof, &terms, &roots);
    assert!(
        !alethe.contains(":rule hole") && !alethe.contains(":rule lia_generic"),
        "the cut chain must be lowered, not left unchecked:\n{alethe}"
    );
    assert!(
        alethe.contains(".c1 (cl ") && alethe.contains("(+ c1 c2 c3 c4)"),
        "expected the checked cut steps, rounding the carry total:\n{alethe}"
    );
    // AY's own round-trip checker (the `--proof-self-check` gate) replays
    // the same document.
    check_alethe_document(
        &alethe,
        &ProblemScope::from_smtlib_source(QF_LIA_CASCADE_CUT_CHAIN_UNSAT),
    )
    .expect("AY's native round-trip checker must accept the cut chain");
    assert_carcara_accepts("cascade_cut_chain", QF_LIA_CASCADE_CUT_CHAIN_UNSAT, &alethe);
}

/// Counterfactual: carcara's verdict rests on each cut being a true rounding.
/// The same document with the carry-total cut raised past what its
/// combination rounds to (`Σ c_i ≥ 5`) is refused.
#[test]
fn carcara_refuses_a_cut_rounded_past_its_combination() {
    let mut terms = TermStore::new();
    let roots = cascade_roots(&mut terms);
    let proof = cut_chain_refutation(&mut terms, &roots);
    let alethe = export_alethe_with_problem_scope(&proof, &terms, &roots);
    assert!(alethe.contains("(>= (+ c1 c2 c3 c4) 4)"), "{alethe}");
    let moved = alethe.replace("(>= (+ c1 c2 c3 c4) 4)", "(>= (+ c1 c2 c3 c4) 5)");
    assert_carcara_verdict(
        "moved_cut_chain",
        QF_LIA_CASCADE_CUT_CHAIN_UNSAT,
        &moved,
        "invalid",
    );
}
