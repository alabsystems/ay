// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#[derive(Clone, Copy)]
struct GuardedRowFixture {
    v: TermId,
    u: TermId,
    w: TermId,
    k: TermId,
}

/// The packed clause `(or (not (= U (store V i x))) (= i k) conclusion)`,
/// refuted as one `kind` lemma against its authored negation. The
/// `conclusion` builder sees the arrays and the probe `k`.
fn guarded_row_proof(
    exec: &mut Executor,
    kind: TheoryLemmaKind,
    conclusion: impl FnOnce(&mut TermStore, GuardedRowFixture) -> TermId,
) -> Proof {
    let array = Sort::array(Sort::Int, Sort::Int);
    let t = &mut exec.ctx.terms;
    let fixture = GuardedRowFixture {
        v: t.mk_var("grw_v", array.clone()),
        u: t.mk_var("grw_u", array.clone()),
        w: t.mk_var("grw_w", array.clone()),
        k: t.mk_var("grw_k", Sort::Int),
    };
    let i = t.mk_var("grw_i", Sort::Int);
    let x = t.mk_var("grw_x", Sort::Int);
    let store = t.mk_app(Symbol::named("store"), [fixture.v, i, x], array);
    let guard_atom = t.mk_app(Symbol::named("="), [fixture.u, store], Sort::Bool);
    let guard = t.mk_not_raw(guard_atom);
    let index = t.mk_app(Symbol::named("="), [i, fixture.k], Sort::Bool);
    let conclusion = conclusion(t, fixture);
    let packed = t.mk_app(Symbol::named("or"), [guard, index, conclusion], Sort::Bool);
    let root = t.mk_not_raw(packed);
    add_authored_roots(exec, &[root]);
    let mut proof = Proof::new();
    let assume = proof.add_assume(root, None);
    let lemma = proof.add_theory_lemma_with_kind("array", vec![packed], kind);
    proof.add_resolution(vec![], packed, lemma, assume);
    proof
}

fn select_int(t: &mut TermStore, array: TermId, index: TermId) -> TermId {
    t.mk_app(Symbol::named("select"), [array, index], Sort::Int)
}

/// The untouched cell `(= (select V k) (select U k))`.
fn untouched_cell(t: &mut TermStore, f: GuardedRowFixture) -> TermId {
    let base = select_int(t, f.v, f.k);
    let read = select_int(t, f.u, f.k);
    t.mk_app(Symbol::named("="), [base, read], Sort::Bool)
}

/// The screen admits exactly the guarded ROW expansion the printer lowers
/// (`ay_proof::checked_guarded_row_expansion_lowering_supported`), as it does
/// for every other printer lowering. Counterfactual: without that screen arm
/// the kind's wire rule is `hole`, and the screen reports this proof's gap.
#[test]
fn the_wire_gap_screen_admits_the_lowered_guarded_row_expansion() {
    let mut exec = Executor::new();
    let proof = guarded_row_proof(
        &mut exec,
        TheoryLemmaKind::ArrayGuardedRowExpansion,
        untouched_cell,
    );
    assert!(exec
        .check_proof_strict_with_datatypes(&proof)
        .is_ok_and(|quality| quality.is_complete()));
    assert!(!exec.proof_has_known_wire_gap(&proof));
}

/// NEGATIVE TWINS: the same valid clause under the unvalidated `Generic`
/// kind, and the label forged onto a falsifiable clause (the untouched cell
/// read from the wrong base `W`), stay known wire gaps.
#[test]
fn the_wire_gap_screen_keeps_unlowered_guarded_rows_as_gaps() {
    let mut exec = Executor::new();
    let generic = guarded_row_proof(&mut exec, TheoryLemmaKind::Generic, untouched_cell);
    assert!(exec.proof_has_known_wire_gap(&generic));
    let mut exec = Executor::new();
    let forged = guarded_row_proof(
        &mut exec,
        TheoryLemmaKind::ArrayGuardedRowExpansion,
        |t, f| {
            let wrong_base = select_int(t, f.w, f.k);
            let read = select_int(t, f.u, f.k);
            t.mk_app(Symbol::named("="), [wrong_base, read], Sort::Bool)
        },
    );
    assert!(exec.check_proof_strict_with_datatypes(&forged).is_err());
    assert!(exec.proof_has_known_wire_gap(&forged));
}
