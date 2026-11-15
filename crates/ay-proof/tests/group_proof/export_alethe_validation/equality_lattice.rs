// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// The all-equality integer lattice lemma (`IntGuardedSplitGap`, zero-split
// case) against the pinned external checker. Each fixture is the minimal
// problem whose three or four authored equalities ARE the lemma: AY's strict
// checker validates the refutation, and the exported document must be
// Carcara `valid` with no allowance — the lemma lowered to `la_generic`, not a
// `hole`.

const QF_LIA_DEEP_RING_LEMMA_UNSAT: &str = r#"
(set-logic QF_LIA)
(declare-const s1 Int)
(declare-const s2 Int)
(declare-const c1 Int)
(declare-const c2 Int)
(declare-const c3 Int)
(assert (= (* 3 s1) (+ (* 4096 c2) s2)))
(assert (= 4096 (+ (* 4096 c1) s1)))
(assert (= (+ s2 500) (+ (* 4096 c3) 1000)))
(check-sat)
"#;

const QF_LIA_PARITY_CHAIN_LEMMA_UNSAT: &str = r#"
(set-logic QF_LIA)
(declare-const a Int)
(declare-const b Int)
(declare-const c Int)
(declare-const s1 Int)
(declare-const s2 Int)
(declare-const k1 Int)
(declare-const k2 Int)
(assert (= (+ (* 256 k1) s1) (+ (* 2 a) (* 2 b))))
(assert (= (+ (* 256 k2) s2) (+ s1 (* 2 c))))
(assert (= s2 (+ (* 256 k1) 127)))
(check-sat)
"#;

fn lattice_int(terms: &mut TermStore, value: i64) -> TermId {
    terms.mk_int(BigInt::from(value))
}

/// `(op args…)` exactly as written, so the printed text is the problem's.
fn lattice_app(terms: &mut TermStore, op: &str, args: &[TermId]) -> TermId {
    let sort = if op == "=" { Sort::Bool } else { Sort::Int };
    terms.mk_app(ay_core::Symbol::named(op), args, sort)
}

/// Assume every root, state the lattice lemma over their negations, and
/// resolve it away root by root.
fn lattice_refutation(terms: &mut TermStore, roots: &[TermId]) -> Proof {
    let mut proof = Proof::new();
    let assumes: Vec<_> = roots
        .iter()
        .map(|&root| proof.add_assume(root, None))
        .collect();
    let negated: Vec<TermId> = roots.iter().map(|&root| terms.mk_not_raw(root)).collect();
    let mut current = proof.add_theory_lemma_with_kind(
        "LIA",
        negated.clone(),
        TheoryLemmaKind::IntGuardedSplitGap,
    );
    for (index, (&root, &assume)) in roots.iter().zip(&assumes).enumerate() {
        current = proof.add_resolution(negated[index + 1..].to_vec(), root, assume, current);
    }
    proof
}

/// `3·s1 = 4096·c2 + s2`, `4096 = 4096·c1 + s1`, `s2 + 500 = 4096·c3 + 1000`.
/// `c1_first` spells the second row's product `(* c1 4096)` internally.
fn deep_ring_roots(terms: &mut TermStore, c1_first: bool) -> (Vec<TermId>, TermId) {
    let s1 = terms.mk_var("s1", Sort::Int);
    let s2 = terms.mk_var("s2", Sort::Int);
    let c1 = terms.mk_var("c1", Sort::Int);
    let c2 = terms.mk_var("c2", Sort::Int);
    let c3 = terms.mk_var("c3", Sort::Int);
    let three = lattice_int(terms, 3);
    let modulus = lattice_int(terms, 4096);
    let three_s1 = lattice_app(terms, "*", &[three, s1]);
    let c2_scaled = lattice_app(terms, "*", &[modulus, c2]);
    let e1_rhs = lattice_app(terms, "+", &[c2_scaled, s2]);
    let e1 = lattice_app(terms, "=", &[three_s1, e1_rhs]);
    let c1_scaled = if c1_first {
        lattice_app(terms, "*", &[c1, modulus])
    } else {
        lattice_app(terms, "*", &[modulus, c1])
    };
    let e2_rhs = lattice_app(terms, "+", &[c1_scaled, s1]);
    let e2 = lattice_app(terms, "=", &[modulus, e2_rhs]);
    let five_hundred = lattice_int(terms, 500);
    let e3_lhs = lattice_app(terms, "+", &[s2, five_hundred]);
    let c3_scaled = lattice_app(terms, "*", &[modulus, c3]);
    let thousand = lattice_int(terms, 1000);
    let e3_rhs = lattice_app(terms, "+", &[c3_scaled, thousand]);
    let e3 = lattice_app(terms, "=", &[e3_lhs, e3_rhs]);
    (vec![e1, e2, e3], e2_rhs)
}

fn assert_lattice_lowered(alethe: &str) {
    assert!(
        !alethe.contains(":rule hole") && !alethe.contains(":rule lia_generic"),
        "the lattice lemma must be lowered, not left unchecked:\n{alethe}"
    );
    assert!(
        alethe.contains(".split (cl (<= ") && alethe.contains(":rule la_generic :args (1 1))"),
        "expected the checked lattice split:\n{alethe}"
    );
}

/// The deep ring row's own t20, needing the multiplier 3 on its second row.
#[test]
fn exports_a_non_unit_multiplier_lattice_lemma_that_carcara_accepts() {
    let mut terms = TermStore::new();
    let (roots, _) = deep_ring_roots(&mut terms, false);
    let proof = lattice_refutation(&mut terms, &roots);
    check_proof_strict(&proof, &terms).expect("the lattice lemma is strictly certified");
    let alethe = export_alethe_with_problem_scope(&proof, &terms, &roots);
    assert_lattice_lowered(&alethe);
    assert!(alethe.contains(":args (1 3 1 1)") || alethe.contains(":args ((- 1) (- 3) (- 1) 1)"));
    assert_carcara_accepts("deep_ring_lattice", QF_LIA_DEEP_RING_LEMMA_UNSAT, &alethe);
}

/// The same lemma whose second row is stored as `(* c1 4096)` and printed in
/// the problem's own spelling `(* 4096 c1)` through the surface channel — the
/// ring rows' actual shape. The printed row is the internal row, so the
/// lowering stands, and every step is checked over the text it ships.
#[test]
fn exports_a_respelled_lattice_lemma_that_carcara_accepts() {
    let mut terms = TermStore::new();
    let (roots, e2_rhs) = deep_ring_roots(&mut terms, true);
    let proof = lattice_refutation(&mut terms, &roots);
    check_proof_strict(&proof, &terms).expect("the lattice lemma is strictly certified");
    let mut overrides: DetHashMap<TermId, String> = det_hash_map_new();
    overrides.insert(e2_rhs, "(+ (* 4096 c1) s1)".to_string());
    let alethe =
        export_alethe_with_problem_scope_and_overrides(&proof, &terms, &roots, Some(&overrides));
    assert_lattice_lowered(&alethe);
    assert_carcara_accepts("respelled_lattice", QF_LIA_DEEP_RING_LEMMA_UNSAT, &alethe);
}

/// A parity chain whose eliminated form is even and equals 127.
#[test]
fn exports_a_parity_chain_lattice_lemma_that_carcara_accepts() {
    let mut terms = TermStore::new();
    let names = ["a", "b", "c", "s1", "s2", "k1", "k2"];
    let v: Vec<TermId> = names.iter().map(|n| terms.mk_var(*n, Sort::Int)).collect();
    let (a, b, c, s1, s2, k1, k2) = (v[0], v[1], v[2], v[3], v[4], v[5], v[6]);
    let two = lattice_int(&mut terms, 2);
    let base = lattice_int(&mut terms, 256);
    let odd = lattice_int(&mut terms, 127);
    let k1_scaled = lattice_app(&mut terms, "*", &[base, k1]);
    let k2_scaled = lattice_app(&mut terms, "*", &[base, k2]);
    let two_a = lattice_app(&mut terms, "*", &[two, a]);
    let two_b = lattice_app(&mut terms, "*", &[two, b]);
    let two_c = lattice_app(&mut terms, "*", &[two, c]);
    let l1 = lattice_app(&mut terms, "+", &[k1_scaled, s1]);
    let r1 = lattice_app(&mut terms, "+", &[two_a, two_b]);
    let l2 = lattice_app(&mut terms, "+", &[k2_scaled, s2]);
    let r2 = lattice_app(&mut terms, "+", &[s1, two_c]);
    let r3 = lattice_app(&mut terms, "+", &[k1_scaled, odd]);
    let roots = vec![
        lattice_app(&mut terms, "=", &[l1, r1]),
        lattice_app(&mut terms, "=", &[l2, r2]),
        lattice_app(&mut terms, "=", &[s2, r3]),
    ];
    let proof = lattice_refutation(&mut terms, &roots);
    check_proof_strict(&proof, &terms).expect("the lattice lemma is strictly certified");
    let alethe = export_alethe_with_problem_scope(&proof, &terms, &roots);
    assert_lattice_lowered(&alethe);
    assert_carcara_accepts(
        "parity_chain_lattice",
        QF_LIA_PARITY_CHAIN_LEMMA_UNSAT,
        &alethe,
    );
}

/// Counterfactual for the three fixtures above: carcara's verdict depends on
/// the lattice content of the split. The exported document with the split's
/// neighbours moved off the lattice (`−499`/`3597` for `−500`/`3596`; the
/// `lo`/`hi` rows move with them, so only the split carries the change) is
/// no longer a checked integer strengthening, and carcara refuses it.
#[test]
fn carcara_refuses_the_lattice_split_with_moved_neighbours() {
    let mut terms = TermStore::new();
    let (roots, _) = deep_ring_roots(&mut terms, false);
    let proof = lattice_refutation(&mut terms, &roots);
    let alethe = export_alethe_with_problem_scope(&proof, &terms, &roots);
    assert_lattice_lowered(&alethe);
    assert!(alethe.contains(" (- 500))") && alethe.contains("(<= 3596 "));
    let moved = alethe
        .replace(" (- 500))", " (- 499))")
        .replace("(<= 3596 ", "(<= 3597 ");
    assert_carcara_verdict(
        "moved_lattice_split",
        QF_LIA_DEEP_RING_LEMMA_UNSAT,
        &moved,
        "invalid",
    );
}
