// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The respelled-pivot arm: one atom printed under two spellings carcara
//! parses to different terms, joined by the `eq_transitive` repair's planner.
//!
//! The shape is `conformance/QF_AX/unsat_store_mismatch.smt2`'s: the assumed
//! `(= (select (store a i v1) i) v2)` is the internal `(= v1 v2)` under its
//! authored override (`mk_select` folded the read), while the negated atom
//! prints through another channel as `(not (= v1 v2))`.

use crate::try_export_alethe_with_problem_scope_and_overrides;
use crate::AlethePrintError;
use ay_core::kani_compat::DetHashMap;
use ay_core::{AletheRule, Proof, ProofId, ProofStep, Sort, Symbol, TermId, TermStore};

/// `p`, the negated atom, a lemma `(cl (not p) atom)`, and two
/// `th_resolution` steps down to the empty clause.
fn refutation(terms: &mut TermStore, p: TermId, atom: TermId, negated: TermId) -> Proof {
    let not_p = terms.mk_not_raw(p);
    let mut built = Proof::new();
    built.add_step(ProofStep::Assume(p));
    built.add_step(ProofStep::Assume(negated));
    let lemma = built.add_rule_step(AletheRule::Hole, vec![not_p, atom], Vec::new(), Vec::new());
    let derived = built.add_rule_step(
        AletheRule::ThResolution,
        vec![atom],
        vec![lemma, ProofId(0)],
        Vec::new(),
    );
    built.add_rule_step(
        AletheRule::ThResolution,
        Vec::new(),
        vec![derived, ProofId(1)],
        Vec::new(),
    );
    built
}

/// `(= v1 v2)` over Int, its raw negation, and `p`.
fn int_atom(terms: &mut TermStore) -> (TermId, TermId, TermId) {
    let p = terms.mk_var("p", Sort::Bool);
    let v1 = terms.mk_var("v1", Sort::Int);
    let v2 = terms.mk_var("v2", Sort::Int);
    let atom = terms.mk_app(Symbol::named("="), [v1, v2], Sort::Bool);
    let negated = terms.mk_not_raw(atom);
    (p, atom, negated)
}

fn export(
    terms: &TermStore,
    proof: &Proof,
    overrides: &[(TermId, &str)],
) -> Result<String, AlethePrintError> {
    let overrides: DetHashMap<TermId, String> = overrides
        .iter()
        .map(|&(term, spelling)| (term, spelling.to_string()))
        .collect();
    let scope: Vec<TermId> = proof
        .steps
        .iter()
        .filter_map(|step| match step {
            ProofStep::Assume(term) => Some(*term),
            _ => None,
        })
        .collect();
    try_export_alethe_with_problem_scope_and_overrides(proof, terms, &scope, Some(&overrides))
}

/// THE DEFECT. Before the arm this was a refused export, `unsat` with no
/// document: "the printed premises do not eliminate the printed resolution
/// pivot, starting at `(= (select (store a i v1) i) v2)`".
#[test]
fn a_read_over_write_pivot_is_bridged_not_refused() {
    let mut terms = TermStore::new();
    let (p, atom, negated) = int_atom(&mut terms);
    let proof = refutation(&mut terms, p, atom, negated);
    let output = export(
        &terms,
        &proof,
        &[
            (atom, "(= (select (store a i v1) i) v2)"),
            (negated, "(not (= v1 v2))"),
        ],
    )
    .expect("the bridged step must export");
    let read = "(select (store a i v1) i)";
    for expected in [
        format!("(step t4.rw.gb0 (cl (= {read} v1)) :rule arrays_idx)"),
        format!(
            "(step t4.rw.gb1 (cl (= (= {read} v2) (= v1 v2))) :rule cong :premises (t4.rw.gb0))"
        ),
        format!(
            "(step t4.rw.p (cl (not (= (= {read} v2) (= v1 v2))) (not (= {read} v2)) (= v1 v2)) \
             :rule equiv_pos2)"
        ),
        "(step t4 (cl) :rule resolution :premises (t3 t4.rw.gb1 t4.rw.p t1))".to_string(),
    ] {
        assert!(
            output.contains(&expected),
            "missing `{expected}`:\n{output}"
        );
    }
}

/// `arrays_idx` concludes the read on the left; when the read is the DENIED
/// spelling the proved equality is the mirror of `(= positive negative)`, and
/// the implication is `equiv_pos1` over that mirror. The denied literal is a
/// lemma's, so no authored-assume bridge confines its spelling first.
#[test]
fn a_mirrored_read_over_write_pivot_uses_equiv_pos1() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let q = terms.mk_var("q", Sort::Bool);
    let negated = terms.mk_not_raw(q);
    let not_p = terms.mk_not_raw(p);
    let mut proof = Proof::new();
    proof.add_step(ProofStep::Assume(p));
    proof.add_step(ProofStep::Assume(q));
    let lemma = proof.add_rule_step(
        AletheRule::Hole,
        vec![not_p, negated],
        Vec::new(),
        Vec::new(),
    );
    let derived = proof.add_rule_step(
        AletheRule::ThResolution,
        vec![negated],
        vec![lemma, ProofId(0)],
        Vec::new(),
    );
    proof.add_rule_step(
        AletheRule::ThResolution,
        Vec::new(),
        vec![derived, ProofId(1)],
        Vec::new(),
    );
    let read = "(select (store ba k q) k)";
    let output = export(
        &terms,
        &proof,
        &[(negated, "(not (select (store ba k q) k))")],
    )
    .expect("the bridged step must export");
    for expected in [
        format!("(step t4.rw.gb0 (cl (= {read} q)) :rule arrays_idx)"),
        format!("(step t4.rw.p (cl (not (= {read} q)) {read} (not q)) :rule equiv_pos1)"),
        "(step t4 (cl) :rule resolution :premises (t1 t4.rw.gb0 t4.rw.p t3))".to_string(),
    ] {
        assert!(
            output.contains(&expected),
            "missing `{expected}`:\n{output}"
        );
    }
}

/// NEGATIVE TWINS. A read `arrays_idx` cannot prove is a genuinely different
/// term (`(select (store a i v1) j)` is `v1` only when `i = j`), so the step
/// keeps its refusal: the arm never turns a divergence it cannot prove into
/// a document.
#[test]
fn a_read_arrays_idx_cannot_prove_keeps_the_refusal() {
    for spelling in [
        "(= (select (store a i v1) j) v2)",
        "(= (select (store a i v3) i) v2)",
    ] {
        let mut terms = TermStore::new();
        let (p, atom, negated) = int_atom(&mut terms);
        let proof = refutation(&mut terms, p, atom, negated);
        let refused = export(
            &terms,
            &proof,
            &[(atom, spelling), (negated, "(not (= v1 v2))")],
        )
        .expect_err("an unprovable respelling must stay refused");
        assert!(
            refused
                .to_string()
                .contains("do not eliminate the printed resolution pivot"),
            "{spelling}: {refused}"
        );
    }
}

/// The differential: aligned spellings replay, and the step renders exactly
/// as it did before the arm existed.
#[test]
fn an_aligned_pivot_renders_unchanged() {
    let mut terms = TermStore::new();
    let (p, atom, negated) = int_atom(&mut terms);
    let proof = refutation(&mut terms, p, atom, negated);
    let output = export(&terms, &proof, &[]).expect("an aligned pivot must export");
    assert!(
        output.contains("(step t4 (cl) :rule th_resolution :premises (t3 t1))"),
        "{output}"
    );
    assert!(!output.contains(".rw."), "{output}");
}
