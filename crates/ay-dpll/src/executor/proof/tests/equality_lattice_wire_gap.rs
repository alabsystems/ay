// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

/// `3·s1 = 4096·c2 + s2`, `4096 = 4096·c1 + s1`, `s2 + 500 = 4096·c3 + target`
/// refuted through one `kind` lemma over the negated roots. `target = 1000`
/// is the deep ring row's t20 (valid only over ℤ); `target = 500` has the
/// model `s1 = s2 = c2 = c3 = 0, c1 = 1`.
fn equality_lattice_proof(exec: &mut Executor, target: i64, kind: TheoryLemmaKind) -> Proof {
    let s1 = exec.ctx.terms.mk_var("lat_s1", Sort::Int);
    let s2 = exec.ctx.terms.mk_var("lat_s2", Sort::Int);
    let c1 = exec.ctx.terms.mk_var("lat_c1", Sort::Int);
    let c2 = exec.ctx.terms.mk_var("lat_c2", Sort::Int);
    let c3 = exec.ctx.terms.mk_var("lat_c3", Sort::Int);
    let t = &mut exec.ctx.terms;
    let three = t.mk_int(BigInt::from(3));
    let modulus = t.mk_int(BigInt::from(4096));
    let five_hundred = t.mk_int(BigInt::from(500));
    let target = t.mk_int(BigInt::from(target));
    let mut app = |op: &str, args: &[TermId]| {
        let sort = if op == "=" { Sort::Bool } else { Sort::Int };
        t.mk_app(Symbol::named(op), args, sort)
    };
    let three_s1 = app("*", &[three, s1]);
    let c2_scaled = app("*", &[modulus, c2]);
    let e1_rhs = app("+", &[c2_scaled, s2]);
    let e1 = app("=", &[three_s1, e1_rhs]);
    let c1_scaled = app("*", &[modulus, c1]);
    let e2_rhs = app("+", &[c1_scaled, s1]);
    let e2 = app("=", &[modulus, e2_rhs]);
    let e3_lhs = app("+", &[s2, five_hundred]);
    let c3_scaled = app("*", &[modulus, c3]);
    let e3_rhs = app("+", &[c3_scaled, target]);
    let e3 = app("=", &[e3_lhs, e3_rhs]);
    let roots = [e1, e2, e3];
    add_authored_roots(exec, &roots);
    let mut proof = Proof::new();
    let assumes: Vec<ProofId> = roots
        .iter()
        .map(|&root| proof.add_assume(root, None))
        .collect();
    let negated: Vec<TermId> = roots
        .iter()
        .map(|&root| exec.ctx.terms.mk_not_raw(root))
        .collect();
    let mut current = proof.add_theory_lemma_with_kind("LIA", negated.clone(), kind);
    for (index, (&root, &assume)) in roots.iter().zip(&assumes).enumerate() {
        current = proof.add_resolution(negated[index + 1..].to_vec(), root, assume, current);
    }
    proof
}

/// The screen admits exactly the lemma the printer lowers.
#[test]
fn the_wire_gap_screen_admits_the_all_equality_lattice_lowering() {
    let mut exec = Executor::new();
    let proof = equality_lattice_proof(&mut exec, 1000, TheoryLemmaKind::IntGuardedSplitGap);
    assert!(exec
        .check_proof_strict_with_datatypes(&proof)
        .is_ok_and(|quality| quality.is_complete()));
    assert!(!exec.proof_has_known_wire_gap(&proof));
}

/// NEGATIVE TWINS: the same valid clause under the unvalidated `Generic`
/// kind, and a forged label on a satisfiable clause, stay known wire gaps.
#[test]
fn the_wire_gap_screen_keeps_unlowered_lattice_lemmas_as_gaps() {
    let mut exec = Executor::new();
    let generic = equality_lattice_proof(&mut exec, 1000, TheoryLemmaKind::Generic);
    assert!(exec.proof_has_known_wire_gap(&generic));
    let mut exec = Executor::new();
    let forged = equality_lattice_proof(&mut exec, 500, TheoryLemmaKind::IntGuardedSplitGap);
    assert!(exec.check_proof_strict_with_datatypes(&forged).is_err());
    assert!(exec.proof_has_known_wire_gap(&forged));
}
