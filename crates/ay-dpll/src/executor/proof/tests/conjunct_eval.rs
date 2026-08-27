// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A preprocessor fold-to-`false` must leave its argument behind.

use super::*;

const DT_PRELUDE: &str = concat!(
    "(set-logic QF_DT)\n",
    "(declare-datatypes ((nat 0)(list 0)(tree 0)) (((succ (pred nat)) (zero))\n",
    "((cons (car tree) (cdr list)) (null))\n",
    "((node (children list)) (leaf (data nat)))\n",
    "))\n",
    "(declare-fun x1 () nat)\n",
    "(declare-fun x3 () list)\n",
    "(declare-fun x4 () list)\n",
);

fn solve(script: &str) -> Executor {
    let commands = parse(script).expect("script parses");
    let mut exec = Executor::new();
    exec.execute_all(&commands).expect("script executes");
    exec
}

/// The one-line `(step t0 (cl) :rule hole)` document: no premises, no
/// derivation, nothing said about the input.
fn is_argument_free(proof: &Proof) -> bool {
    matches!(
        proof.steps.as_slice(),
        [ProofStep::Step {
            rule: AletheRule::Hole | AletheRule::Trust,
            ..
        }]
    )
}

fn sole_assume(terms: &TermStore, proof: &Proof) -> TermId {
    let assumes: Vec<TermId> = proof
        .steps
        .iter()
        .filter_map(|step| match step {
            ProofStep::Assume(term) => Some(*term),
            _ => None,
        })
        .collect();
    assert_eq!(assumes.len(), 1, "the rebuild assumes exactly one root");
    assert!(
        !matches!(
            terms.get(assumes[0]),
            TermData::Const(Constant::Bool(false))
        ),
        "the premise must be the authored assertion, never the folded constant",
    );
    assumes[0]
}

/// QF_DT `typed_v2l20006`, verbatim in shape: ONE `assert`, whose first
/// conjunct is a tester applied to a term literally built with that
/// constructor. Preprocessing evaluates it, folds the whole assertion to
/// `false`, and keeps no record — so the proof rested on an `assume false`
/// and was erased to a one-line hole. It has an argument; record it.
#[test]
fn a_datatype_tester_fold_records_its_argument() {
    let exec = solve(&format!(
        "{DT_PRELUDE}(assert (and (not ((_ is leaf) (leaf x1))) (not (= x3 x4))))\n(check-sat)\n"
    ));
    assert!(exec.last_result_is_unsat(), "the instance is unsat");
    let proof = exec.last_proof.as_ref().expect("a proof is retained");
    assert!(
        !is_argument_free(proof),
        "a refutation with a recoverable argument must not publish as a bare hole",
    );
    let root = sole_assume(&exec.ctx.terms, proof);
    assert!(
        matches!(
            exec.ctx.terms.get(root),
            TermData::App(Symbol::Named(name), args) if name == "and" && args.len() == 2
        ),
        "the premise is the authored conjunction",
    );
    assert!(
        proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::TheoryLemma {
                kind: TheoryLemmaKind::DatatypeTesterEval,
                ..
            }
        )),
        "the one obligation Alethe cannot spell must be NAMED, not anonymous",
    );
    assert!(
        Executor::proof_derives_empty_clause(proof),
        "the derivation must actually close",
    );
}

/// The same defect closed by a rule external checkers DO implement. The
/// refuting conjunct is syntactic reflexivity — QF_DT `typed_v1l80035`'s first
/// conjunct is exactly `(not (= (succ zero) (succ zero)))` — so the whole
/// document is checkable, with no theory step at all.
#[test]
fn a_reflexive_disequality_fold_records_a_fully_checkable_argument() {
    let exec = solve(&format!(
        "{DT_PRELUDE}(assert (and (not (= (succ zero) (succ zero))) (= x3 x4)))\n(check-sat)\n"
    ));
    assert!(exec.last_result_is_unsat(), "the instance is unsat");
    let proof = exec.last_proof.as_ref().expect("a proof is retained");
    assert!(!is_argument_free(proof), "the argument must be recorded");
    let _ = sole_assume(&exec.ctx.terms, proof);
    assert!(
        proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::Step {
                rule: AletheRule::EqReflexive | AletheRule::Refl,
                ..
            }
        )),
        "reflexivity is checkable Alethe and must be spelled as such",
    );
    assert!(
        !proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::Step {
                rule: AletheRule::Trust | AletheRule::Hole,
                ..
            } | ProofStep::TheoryLemma {
                kind: TheoryLemmaKind::Generic,
                ..
            }
        )),
        "this class needs no trust step and no hole",
    );
}

/// The conjunct need not be at the top level: the family nests its `and`s
/// left-associatively, so the refuting leaf sits several levels down. The
/// projection is an `and_pos` chain, one strictly-validated step per level.
#[test]
fn a_nested_conjunct_is_projected_through_the_and_tree() {
    let exec = solve(&format!(
        "{DT_PRELUDE}(assert (and (and (and (not ((_ is leaf) (leaf x1))) (= x3 x3)) (= x4 x4)) (= x3 x3)))\n(check-sat)\n"
    ));
    assert!(exec.last_result_is_unsat(), "the instance is unsat");
    let proof = exec.last_proof.as_ref().expect("a proof is retained");
    assert!(!is_argument_free(proof), "the argument must be recorded");
    let and_pos_steps = proof
        .steps
        .iter()
        .filter(|step| {
            matches!(
                step,
                ProofStep::Step {
                    rule: AletheRule::AndPos(_),
                    ..
                }
            )
        })
        .count();
    assert!(
        and_pos_steps >= 3,
        "one and_pos per level of the authored tree, got {and_pos_steps}",
    );
}

/// FAIL-CLOSED, and the reason this gate exists at all.
///
/// The author writes `(leaf zero)` and also writes an `ite` that FOLDS to
/// `(leaf zero)`. Both spellings share one hash-consed `TermId`, so the
/// printer's surface-override table renders BOTH with the `ite` spelling, and
/// the rebuilt premise no longer prints as anything in the problem file.
/// Measured with carcara on the artifact this produced before the gate:
///
/// ```text
/// [ERROR] checking failed on step 't0' with rule 'assume': could not match
///         term to any of the original problem premises: (and (not (= (ite ...
/// invalid
/// ```
///
/// `invalid` is strictly worse than the one-line hole it replaced — a wrong
/// proof is worse than no proof — so a premise that does not print back as the
/// author's own assertion must decline.
#[test]
fn a_premise_that_does_not_print_as_authored_is_declined() {
    let mut exec = solve(&format!(
        "{DT_PRELUDE}(assert (and (not (= (ite ((_ is cons) null) (car null) (leaf zero)) (leaf zero))) (not ((_ is cons) (cons (leaf x1) null)))))\n(check-sat)\n"
    ));
    let mut probe = Proof::new();
    probe.add_rule_step(AletheRule::Hole, Vec::new(), Vec::new(), Vec::new());
    assert!(
        !exec.replace_with_exact_authored_conjunct_eval_refutation(&mut probe),
        "the rebuilt premise renders with a spelling the problem file does not contain",
    );
    assert!(
        is_argument_free(&probe),
        "declining must leave the proof byte-identical",
    );
}

/// FAIL-CLOSED. The rebuild fires only where a conjunct is false BY
/// EVALUATION. An unsat instance whose refutation needs real datatype
/// reasoning across two assertions has no such conjunct, and this pass must
/// decline rather than invent one.
#[test]
fn a_refutation_without_a_self_false_conjunct_is_declined() {
    let mut exec = solve(&format!(
        "{DT_PRELUDE}(declare-fun t () tree)\n(assert (and ((_ is leaf) t) (= x3 x4)))\n(assert ((_ is node) t))\n(check-sat)\n"
    ));
    let mut probe = Proof::new();
    probe.add_rule_step(AletheRule::Hole, Vec::new(), Vec::new(), Vec::new());
    assert!(
        !exec.replace_with_exact_authored_conjunct_eval_refutation(&mut probe),
        "no conjunct of either assertion evaluates to false on its own",
    );
    assert!(
        is_argument_free(&probe),
        "a declined rebuild must leave the proof byte-identical",
    );
}
