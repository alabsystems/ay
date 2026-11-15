// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! REACHABILITY and EXACT WIRE TEXT for the shared-quantifier fold promoter.
//!
//! `authored_shared_tautology` recovers a class the two binder-free promoters
//! in `authored_fold_to_false_refutation` cannot see at all. Alpha-quantifier
//! sharing makes two syntactically identical authored quantifiers ONE term,
//! and `mk_and`'s complement scan then folds `(not (=> H G))` to the constant
//! `false` whenever a conjunct of `H` is also the innermost consequent of `G`.
//! The authored root gets no `TermId`, the fold keeps no derivation, and the
//! whole document was erased to `(step t0 (cl) :rule hole)`.
//!
//! Measured on this fixture at `ec898d4575`: `unsat` under `--no-proof`,
//! `--rigor fast`, `--competition` and `--z3-mode`; `unknown` under the
//! default `--rigor standard` and under `--rigor certified`.

use ay_dpll::Executor;
use ay_frontend::parse;

fn run_with_proofs(body: &str) -> (Vec<String>, Option<String>) {
    let script = format!("(set-option :produce-proofs true)\n{body}");
    let commands = parse(&script).expect("fixture script must parse");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("fixture script must run");
    let proof = if outputs.last().map(String::as_str) == Some("unsat") {
        let get_proof = parse("(get-proof)").expect("(get-proof) must parse");
        exec.execute_all(&get_proof)
            .ok()
            .and_then(|out| out.last().cloned())
    } else {
        None
    };
    (outputs, proof)
}

/// `(id, premises, is_empty_clause)` for every `assume` / `step` line.
fn proof_steps(proof: &str) -> Vec<(String, Vec<String>, bool)> {
    proof
        .lines()
        .filter_map(|line| {
            let line = line.trim();
            let body = line
                .strip_prefix("(step ")
                .or_else(|| line.strip_prefix("(assume "))?;
            let id = body.split_whitespace().next()?.to_string();
            let premises = line
                .split_once(":premises (")
                .and_then(|(_, tail)| tail.split_once(')'))
                .map(|(inside, _)| inside.split_whitespace().map(str::to_string).collect())
                .unwrap_or_default();
            Some((id, premises, line.contains(" (cl) ")))
        })
        .collect()
}

/// Every step the EMPTY clause rests on, TRANSITIVELY. "`t0` occurs somewhere
/// in the document" is not the property under test: a dead `assume` the
/// refutation never consumes satisfies that while the empty clause still comes
/// from nowhere.
fn empty_clause_support(proof: &str) -> Vec<String> {
    let steps = proof_steps(proof);
    let mut pending: Vec<String> = steps
        .iter()
        .filter(|(_, _, empty)| *empty)
        .map(|(id, _, _)| id.clone())
        .collect();
    let mut support: Vec<String> = Vec::new();
    while let Some(id) = pending.pop() {
        if support.contains(&id) {
            continue;
        }
        support.push(id.clone());
        if let Some((_, premises, _)) = steps.iter().find(|(step, _, _)| *step == id) {
            pending.extend(premises.iter().cloned());
        }
    }
    support
}

/// The published document, byte for byte.
///
/// Pinned as BYTES, not as a rule-name `contains`, for the reason the sibling
/// module's table records: AY's own strict checker accepting a candidate says
/// nothing about what the PRINTER then writes, and this campaign has shipped
/// green flags on documents that differed from the object the checker
/// validated. Two details here are load-bearing and invisible to any looser
/// assertion.
///
/// * The `assume` spells the binder `((n Int))` — the AUTHOR's name.
///   Elaboration alpha-renames it to `n_2`, and a document spelling it that
///   way is one Carcara refuses at its first premise ("could not match term to
///   any of the original problem premises") — strictly worse than the bare
///   hole this replaces.
/// * `and_pos` carries `:args (0)`, the INDEX. Measured against pinned Carcara
///   1.1.0: with no `:args` it answers "expected 1 arguments, got 0"; with the
///   `and`-TERM as the argument, "expected term ... to be an non-negative
///   integer constant". Only the index checks.
const PUBLISHED: &str = "\
(assume t0 (not (=> (and (=> a (forall ((n Int)) (f n))) r) (=> r (=> a (forall ((n Int)) (f n)))))))\n\
(step t1 (cl (and (=> a (forall ((n Int)) (f n))) r)) :rule not_implies1 :premises (t0))\n\
(step t2 (cl (not (and (=> a (forall ((n Int)) (f n))) r)) (=> a (forall ((n Int)) (f n)))) :rule and_pos :args (0))\n\
(step t3 (cl (=> a (forall ((n Int)) (f n)))) :rule resolution :premises (t2 t1))\n\
(step t4 (cl (not (=> r (=> a (forall ((n Int)) (f n)))))) :rule not_implies2 :premises (t0))\n\
(step t5 (cl (not (=> a (forall ((n Int)) (f n))))) :rule not_implies2 :premises (t4))\n\
(step t6 (cl) :rule resolution :premises (t5 t3))";

const SHARED: &str = "\
(set-logic UFLIA)\n\
(declare-fun a () Bool)\n\
(declare-fun r () Bool)\n\
(declare-fun f (Int) Bool)\n\
(assert (not (=> (and (=> a (forall ((n Int)) (f n))) r)\n\
                 (=> r (=> a (forall ((n Int)) (f n)))))))\n\
(check-sat)\n";

/// The SAME script with the second quantifier's body over a different symbol,
/// so the two quantifiers are not one term.
const MUTANT: &str = "\
(set-logic UFLIA)\n\
(declare-fun a () Bool)\n\
(declare-fun r () Bool)\n\
(declare-fun f (Int) Bool)\n\
(declare-fun g (Int) Bool)\n\
(assert (not (=> (and (=> a (forall ((n Int)) (f n))) r)\n\
                 (=> r (=> a (forall ((n Int)) (g n)))))))\n\
(check-sat)\n";

#[test]
fn a_shared_quantifier_fold_publishes_the_exact_propositional_refutation() {
    let (outputs, proof) = run_with_proofs(SHARED);
    assert_eq!(
        outputs.last().map(String::as_str),
        Some("unsat"),
        "the shared-quantifier fold must publish its verdict"
    );
    let proof = proof.expect("an unsat verdict under :produce-proofs must carry a proof");
    assert_eq!(
        proof.trim(),
        PUBLISHED,
        "the published document must be the fold's own argument, byte for byte"
    );
    assert!(
        empty_clause_support(&proof).contains(&"t0".to_string()),
        "the empty clause must rest on the authored assume, transitively"
    );
    assert!(
        !proof.contains(":rule hole") && !proof.contains(":rule trust"),
        "the published document must carry no hole and no trust step"
    );
}

/// A conjunct reachable only through a UNIT `(and X)`.
///
/// Alethe's `and_pos` names one conjunct of a FLAT conjunction and the printer
/// enforces that literally, so a 1-ary source is unprintable. AY's strict
/// checker and the export-scope check both ACCEPT the 1-ary step, so before
/// the arity guard the pass committed a candidate that passed every gate and
/// was then refused by the render: `--proof FILE` exited 1 publishing no
/// verdict at all, and the default posture emitted no artifact where the base
/// still wrote its holey one — the one outcome this pass promises never to
/// produce.
const UNIT_AND: &str = "\
(set-logic UFLIA)\n\
(declare-fun a () Bool)\n\
(declare-fun r () Bool)\n\
(declare-fun f (Int) Bool)\n\
(assert (not (=> (and r (and (=> a (forall ((n Int)) (f n)))))\n\
                 (=> r (=> a (forall ((n Int)) (f n)))))))\n\
(check-sat)\n";

/// The pass must DECLINE here rather than commit something the printer will
/// refuse, and the query must end exactly where the base leaves it.
///
/// Under an explicit artifact demand this fixture is `unknown` on the base
/// too — the pre-existing mandatory-artifact trap, not this pass. What the
/// defect added was a HARD failure on top of it: measured at `11172f75f3`,
/// `ay --proof out.alethe` published no verdict and exited 1 with
/// "invalid surface proof step t4: and_pos source is not a flat Boolean
/// and-term", and the default posture emitted no artifact where the base
/// wrote a holey one.
#[test]
fn a_conjunct_behind_a_unit_and_is_declined_not_committed() {
    let (outputs, proof) = run_with_proofs(UNIT_AND);
    assert_eq!(
        outputs.last().map(String::as_str),
        Some("unknown"),
        "under an explicit artifact demand this fixture is `unknown`, as on the base"
    );
    assert!(
        proof.is_none(),
        "a verdict that was withheld cannot carry a proof"
    );

    // Without the artifact demand the verdict is published, and the document
    // is the bare hole this pass could not improve on — never an `and_pos`
    // step over a unit conjunction.
    let commands = ay_frontend::parse(UNIT_AND).expect("fixture must parse");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("fixture must run");
    assert_eq!(
        outputs.last().map(String::as_str),
        Some("unsat"),
        "the verdict itself is unaffected — only the argument is unavailable"
    );
}

/// FALSIFY-ONCE at the PRODUCT boundary. The promoter's whole soundness
/// argument is that the two authored quantifiers are ONE term and that the
/// final resolution DISCHARGES that identity rather than asserting it. Break
/// it by one symbol and the recovery must disappear entirely — no refutation.
/// If this ever reports `unsat`, the pass is inventing a refutation the
/// problem does not have.
///
/// The mutant is satisfiable (`a`, `r` true, `f` true everywhere, `g` false
/// somewhere; z3 5.1.0 `sat`). It was `unknown` until the quantified model
/// check (2026-09-30) completed `f` and `g` and decided it, so `sat` is the
/// other acceptable answer; neither carries a proof.
#[test]
fn a_fold_whose_quantifiers_differ_by_one_symbol_publishes_nothing() {
    let (outputs, proof) = run_with_proofs(MUTANT);
    let verdict = outputs.last().map(String::as_str);
    assert!(
        matches!(verdict, Some("unknown" | "sat")),
        "with the shared identity broken there is no fold and no refutation; got {verdict:?}"
    );
    assert!(
        proof.is_none(),
        "no refutation was reached, so no proof may be published"
    );
}
