// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

/// The packed `Int` chain `(or (not (= a b)) (= a c) (not (= b c)))` — the
/// `storeinv_sf_size5` mechanism, conclusion NOT last — refuted as one `kind`
/// lemma carrying `farkas` against its authored negation, and that negation
/// (the export's problem scope). `broken` re-points the second link at `d`,
/// so no chain reaches `c` and the clause is falsifiable.
fn arith_chain_proof(
    exec: &mut Executor,
    kind: TheoryLemmaKind,
    broken: bool,
    farkas: Option<FarkasAnnotation>,
) -> (Proof, TermId) {
    let t = &mut exec.ctx.terms;
    let [a, b, c, d] = ["ach_a", "ach_b", "ach_c", "ach_d"].map(|name| t.mk_var(name, Sort::Int));
    let ab = t.mk_app(Symbol::named("="), [a, b], Sort::Bool);
    let first = t.mk_not_raw(ab);
    let conclusion = t.mk_app(Symbol::named("="), [a, c], Sort::Bool);
    let link = t.mk_app(
        Symbol::named("="),
        [b, if broken { d } else { c }],
        Sort::Bool,
    );
    let second = t.mk_not_raw(link);
    let packed = t.mk_app(Symbol::named("or"), [first, conclusion, second], Sort::Bool);
    let root = t.mk_not_raw(packed);
    add_authored_roots(exec, &[root]);
    let mut proof = Proof::new();
    let assume = proof.add_assume(root, None);
    let lemma =
        proof.add_theory_lemma_with_farkas_and_kind_opt("arith", vec![packed], farkas, kind);
    proof.add_resolution(vec![], packed, lemma, assume);
    (proof, root)
}

/// `proof` as the exporter prints it over the problem `scope`.
fn arith_chain_wire(exec: &Executor, proof: &Proof, scope: &[TermId]) -> String {
    let printed = ay_proof::try_export_alethe_with_problem_scope_and_overrides(
        proof,
        &exec.ctx.terms,
        scope,
        None,
    );
    assert!(printed.is_ok(), "the fixture prints: {printed:?}");
    printed.unwrap_or_default()
}

/// The screen admits exactly the equality chain the printer lowers
/// (`ay_proof::arith_equality_chain_lowering_supported`), as it does for every
/// other printer lowering. Counterfactual: without that screen arm every
/// arithmetic lane declines this clause, the kind's wire rule is `hole`, and
/// the screen reports this proof's gap.
#[test]
fn the_wire_gap_screen_admits_the_lowered_arith_equality_chain() {
    let mut exec = Executor::new();
    let (proof, root) = arith_chain_proof(
        &mut exec,
        TheoryLemmaKind::ArithClauseTautology,
        false,
        None,
    );
    assert!(exec
        .check_proof_strict_with_datatypes(&proof)
        .is_ok_and(|quality| quality.is_complete()));
    let wire = arith_chain_wire(&exec, &proof, &[root]);
    assert!(!wire.contains(":rule hole"), "{wire}");
    assert!(!exec.proof_has_known_wire_gap(&proof));
}

/// NEGATIVE TWINS: the same valid clause under the unvalidated `Generic`
/// kind, and the label forged onto a broken chain, stay known wire gaps.
#[test]
fn the_wire_gap_screen_keeps_unlowered_arith_chains_as_gaps() {
    let mut exec = Executor::new();
    let (generic, _) = arith_chain_proof(&mut exec, TheoryLemmaKind::Generic, false, None);
    assert!(exec.proof_has_known_wire_gap(&generic));
    let mut exec = Executor::new();
    let (forged, _) =
        arith_chain_proof(&mut exec, TheoryLemmaKind::ArithClauseTautology, true, None);
    assert!(exec.check_proof_strict_with_datatypes(&forged).is_err());
    assert!(exec.proof_has_known_wire_gap(&forged));
}

/// NEGATIVE TWIN of the arm's precedence: the printer prints a Farkas-
/// annotated lemma through its Farkas lane before it reaches the chain arm,
/// and that lane ships this kind as `hole`, so an annotated chain must stay a
/// known gap. (The strict `ArithClauseTautology` arm re-derives the clause and
/// ignores the annotation, so the proof is still complete.) Counterfactual:
/// without the screen arm's `farkas.is_none()` the screen admits this proof
/// while its export carries the hole.
#[test]
fn the_wire_gap_screen_keeps_a_farkas_annotated_arith_chain_as_a_gap() {
    let mut exec = Executor::new();
    let annotation = FarkasAnnotation::from_ints(&[1]);
    let (proof, root) = arith_chain_proof(
        &mut exec,
        TheoryLemmaKind::ArithClauseTautology,
        false,
        Some(annotation),
    );
    assert!(exec
        .check_proof_strict_with_datatypes(&proof)
        .is_ok_and(|quality| quality.is_complete()));
    let wire = arith_chain_wire(&exec, &proof, &[root]);
    assert!(wire.contains(":rule hole"), "{wire}");
    assert!(exec.proof_has_known_wire_gap(&proof));
}

/// `chains` packed `Int` chains, then the unit `(+ x 0) = x` that only
/// `poly_simp` lowers, refuted against its negation; and the terms whose
/// symbols the export must declare.
fn arith_chain_budget_proof(exec: &mut Executor, chains: usize) -> (Proof, Vec<TermId>) {
    let mut proof = Proof::new();
    let mut scope = Vec::new();
    for index in 0..chains {
        let t = &mut exec.ctx.terms;
        let [a, b, c] =
            ["a", "b", "c"].map(|name| t.mk_var(format!("acb_{name}{index}"), Sort::Int));
        let ab = t.mk_app(Symbol::named("="), [a, b], Sort::Bool);
        let bc = t.mk_app(Symbol::named("="), [b, c], Sort::Bool);
        let ac = t.mk_app(Symbol::named("="), [a, c], Sort::Bool);
        let [nab, nbc] = [t.mk_not_raw(ab), t.mk_not_raw(bc)];
        let packed = t.mk_app(Symbol::named("or"), [nab, nbc, ac], Sort::Bool);
        scope.push(packed);
        proof.add_theory_lemma_with_kind(
            "arith",
            vec![packed],
            TheoryLemmaKind::ArithClauseTautology,
        );
    }
    let t = &mut exec.ctx.terms;
    let x = t.mk_var("acb_x", Sort::Int);
    let zero = t.mk_int(BigInt::from(0));
    let sum = t.mk_app(Symbol::named("+"), [x, zero], Sort::Int);
    let identity = t.mk_eq(sum, x);
    let root = t.mk_not_raw(identity);
    scope.push(root);
    let assume = proof.add_assume(root, None);
    let lemma = proof.add_theory_lemma_with_kind(
        "arith",
        vec![identity],
        TheoryLemmaKind::ArithClauseTautology,
    );
    proof.add_resolution(vec![], identity, assume, lemma);
    (proof, scope)
}

/// The screen spends the proof-wide `poly_simp` allowance as the printer
/// does. The printer reaches its chain arm only after `poly_simp` and the
/// structural lanes have each spent an attempt, so eight chains exhaust the
/// sixteen and the identity after them prints as `hole`; the screen must
/// report that gap. Counterfactual: with the screen's chain arm asked BEFORE
/// its `poly_simp` ask, the screen admits the eight-chain proof (no known
/// gap) while the export carries the hole.
#[test]
fn the_wire_gap_screen_spends_the_poly_simp_allowance_the_printer_spends() {
    for (chains, holes) in [(7, 0), (8, 1)] {
        let mut exec = Executor::new();
        let (proof, scope) = arith_chain_budget_proof(&mut exec, chains);
        assert!(ay_proof::check_proof_strict(&proof, &exec.ctx.terms)
            .is_ok_and(|quality| quality.is_complete()));
        let wire = arith_chain_wire(&exec, &proof, &scope);
        assert_eq!(
            wire.matches(":rule eq_transitive").count(),
            chains,
            "{wire}"
        );
        assert_eq!(wire.matches(":rule hole").count(), holes, "{wire}");
        assert_eq!(
            exec.proof_has_known_wire_gap(&proof),
            holes > 0,
            "chains={chains}: the screen and the printer disagree\n{wire}"
        );
    }
}
