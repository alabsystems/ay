// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Coverage for the CONJUNCT-BY-CONJUNCT decomposition lane.
//!
//! This file owns the FIXTURES, the positive end-to-end path and the WIRE
//! check. `conjunct_decomposition_leaf_guard_tests.rs` owns the guard mutation
//! ledger and `conjunct_decomposition_leaf_negative_tests.rs` owns the
//! adversarial negatives, each with a falsifying assignment CHECKED in-test by
//! an independent evaluator.
//!
//! **Every fixture is a COMPLETE REFUTATION** and asserts, before running the
//! lane, both that it starts REJECTED and that the SIBLING whole-term lane
//! declines it — otherwise the test would be measuring the wrong lane.

use ay_core::{AletheRule, Proof, ProofId, ProofStep, Sort, TermData, TermId};
use ay_frontend::parse;

use crate::Executor;

/// The residual class in miniature. The authored root is a THREE-conjunct
/// conjunction whose conjuncts are, in some order:
///
/// * `(ff (and g h) k)` — a compound Boolean argument at an `App` position;
/// * `(not (ff (and g h) m))` — the SAME compound argument, but underneath a
///   `not`. This is the position `ay_proof::congruence_forest` refuses to
///   descend, and it is the whole reason this lane exists;
/// * `(ff k m)` — no compound argument at all, so this conjunct is UNCHANGED
///   in the rewrite and must come out of the `and_pos` descent alone.
pub(super) const CONJUNCTS: &str = r#"
    (set-logic QF_UF)
    (declare-fun g () Bool)
    (declare-fun h () Bool)
    (declare-fun k () Bool)
    (declare-fun m () Bool)
    (declare-fun zz () Bool)
    (declare-fun ff (Bool Bool) Bool)
    (assert (and (ff (and g h) k) (not (ff (and g h) m)) (ff k m)))
    (assert zz)
    (assert (not zz))
    (check-sat)
"#;

/// A solve in the CENSUS REGIME: `set_retain_parsed_assertions(false)`, exactly
/// what the CLI does for `--no-proof`, `--z3-mode` and competition mode.
pub(super) fn solve(text: &str) -> Executor {
    let commands = parse(text).expect("parse");
    let mut exec = Executor::new();
    exec.set_retain_parsed_assertions(false);
    assert_eq!(exec.execute_all(&commands).expect("exec"), vec!["unsat"]);
    exec
}

pub(super) fn boolvar(exec: &mut Executor, name: &str) -> TermId {
    exec.ctx.terms.mk_var(name, Sort::Bool)
}

/// The authored `and` root, taken from the STRICT SCOPE so a test cannot
/// disagree with the solver about what was authored — or about the ORDER
/// `mk_and`'s sort put its conjuncts in.
pub(super) fn authored_and_root(exec: &Executor) -> TermId {
    exec.complete_problem_assertions_for_strict_proof()
        .into_iter()
        .find(|&term| {
            matches!(
                exec.ctx.terms.get(term),
                TermData::App(ay_core::Symbol::Named(name), args)
                    if name == "and" && args.len() == 3
            )
        })
        .expect("the fixture's root must be in the strict scope")
}

pub(super) fn conjuncts_of(exec: &Executor, term: TermId) -> Vec<TermId> {
    match exec.ctx.terms.get(term) {
        TermData::App(ay_core::Symbol::Named(name), args) if name == "and" => args.clone(),
        other => panic!("not an `and` application: {other:?}"),
    }
}

/// Structurally rebuild `term` with every occurrence of `from` replaced by
/// `to`, descending `App` and `Not` and nothing else.
///
/// Deliberately NOT `mk_and`/`mk_not`: `mk_and` flattens, sorts and dedups, and
/// `mk_not` normalises De Morgan, so either would rebuild a DIFFERENT term than
/// the producer's substitution does.
pub(super) fn substitute(exec: &mut Executor, term: TermId, from: TermId, to: TermId) -> TermId {
    if term == from {
        return to;
    }
    match exec.ctx.terms.get(term).clone() {
        TermData::App(symbol, args) => {
            let sort = exec.ctx.terms.sort(term).clone();
            let rebuilt: Vec<TermId> = args
                .into_iter()
                .map(|arg| substitute(exec, arg, from, to))
                .collect();
            exec.ctx.terms.mk_app(symbol, rebuilt, sort)
        }
        TermData::Not(inner) => {
            let rebuilt = substitute(exec, inner, from, to);
            exec.ctx.terms.mk_not_raw(rebuilt)
        }
        _ => term,
    }
}

/// The leaf the purification produces: the authored root with `(and g h)`
/// replaced by a symbol the problem never mentions, at BOTH occurrences —
/// including the one underneath the `not`.
pub(super) fn purified_leaf(exec: &mut Executor) -> (TermId, TermId, TermId) {
    let root = authored_and_root(exec);
    let g = boolvar(exec, "g");
    let h = boolvar(exec, "h");
    let definiens = exec.ctx.terms.mk_and(vec![g, h]);
    let pp = boolvar(exec, "pp");
    let leaf = substitute(exec, root, definiens, pp);
    assert_ne!(leaf, root, "the substitution must change something");
    (leaf, root, pp)
}

/// The SYNTACTIC complement of `literal`.
pub(super) fn complement(exec: &mut Executor, literal: TermId) -> TermId {
    let normalized = exec.ctx.terms.mk_not(literal);
    let cancels = match exec.ctx.terms.get(normalized) {
        TermData::Not(inner) => *inner == literal,
        _ => matches!(exec.ctx.terms.get(literal), TermData::Not(inner) if *inner == normalized),
    };
    if cancels {
        normalized
    } else {
        exec.ctx.terms.mk_not_raw(literal)
    }
}

/// A COMPLETE REFUTATION carrying `goal` as its premiseless `trust` leaf.
///
/// The CLOSER is a second `trust` step, not an `assume`: freshness is decided
/// against the FINISHED proof's `assume` set, so an `assume (not goal)` would
/// itself mention the fresh definiendum and every mint would decline for a
/// reason that is not the one under test. Same discipline as the sibling lane's
/// fixtures, and for the same measured reason.
pub(super) fn leaf_proof(exec: &mut Executor, goal: TermId) -> Proof {
    let negated = complement(exec, goal);
    let mut proof = Proof::new();
    proof.steps.push(ProofStep::Step {
        rule: AletheRule::Trust,
        clause: vec![goal],
        premises: Vec::new(),
        args: Vec::new(),
    });
    proof.steps.push(ProofStep::Step {
        rule: AletheRule::Trust,
        clause: vec![negated],
        premises: Vec::new(),
        args: Vec::new(),
    });
    proof.steps.push(ProofStep::Step {
        rule: AletheRule::Resolution,
        clause: Vec::new(),
        premises: vec![ProofId(0), ProofId(1)],
        args: Vec::new(),
    });
    proof
}

pub(super) fn premiseless_unit_trust_leaves(proof: &Proof) -> usize {
    proof
        .steps
        .iter()
        .filter(|step| {
            matches!(
                step,
                ProofStep::Step {
                    rule: AletheRule::Trust,
                    clause,
                    premises,
                    args,
                } if premises.is_empty() && args.is_empty() && clause.len() == 1
            )
        })
        .count()
}

pub(super) fn count_rule(proof: &Proof, wanted: &AletheRule) -> usize {
    proof
        .steps
        .iter()
        .filter(|step| matches!(step, ProofStep::Step { rule, .. } if rule == wanted))
        .count()
}

pub(super) fn assume_count(proof: &Proof) -> usize {
    proof
        .steps
        .iter()
        .filter(|step| matches!(step, ProofStep::Assume(_)))
        .count()
}

/// A comparable rendering of a proof's steps. `ProofStep` has no `PartialEq`.
pub(super) fn shape(proof: &Proof) -> String {
    format!("{:?}", proof.steps)
}

/// This lane's entry point, run against the executor's strict scope.
pub(super) fn rerun(exec: &mut Executor, proof: &mut Proof) -> usize {
    let scope = exec.complete_problem_assertions_for_strict_proof();
    exec.derive_conjunctwise_decomposed_leaves(proof, &scope)
}

/// The lane's entry point with an EXPLICIT handed scope, so a test can make the
/// two authored scopes DIFFER — which is the only way the pool's INTERSECTION
/// rule is observable at all.
pub(super) fn rerun_with_scope(exec: &mut Executor, proof: &mut Proof, scope: &[TermId]) -> usize {
    exec.derive_conjunctwise_decomposed_leaves(proof, scope)
}

/// The SIBLING whole-term lane's entry point, so every fixture can show it
/// declines.
pub(super) fn rerun_sibling(exec: &mut Executor, proof: &mut Proof) -> usize {
    let scope = exec.complete_problem_assertions_for_strict_proof();
    exec.derive_leaves_over_minted_definitions(proof, &scope)
}

// ===== the lane, on a hand-built leaf over a REAL SOLVE =====

/// THE POSITIVE PATH, and the two-sided statement of what this lane owns: the
/// whole-term minting lane DECLINES this leaf (its alignment stops at the
/// `not`), and this one takes it.
#[test]
fn a_leaf_that_differs_under_a_not_is_derived_conjunct_by_conjunct() {
    let mut exec = solve(CONJUNCTS);
    let (atom, root, _) = purified_leaf(&mut exec);

    // The sibling lane, on its own copy: it must decline, or this fixture is
    // not the residual class.
    let mut sibling_proof = leaf_proof(&mut exec, atom);
    let before = shape(&sibling_proof);
    assert_eq!(
        rerun_sibling(&mut exec, &mut sibling_proof),
        0,
        "the whole-term lane cannot descend the `not` and must decline"
    );
    assert_eq!(
        shape(&sibling_proof),
        before,
        "a declined lane must leave the proof byte-identical"
    );

    let mut proof = leaf_proof(&mut exec, atom);
    assert!(
        exec.check_proof_strict_with_datatypes(&proof).is_err(),
        "the fixture must start REJECTED"
    );
    assert_eq!(
        premiseless_unit_trust_leaves(&proof),
        2,
        "the leaf and its trust closer"
    );

    assert_eq!(rerun(&mut exec, &mut proof), 1);
    assert_eq!(
        premiseless_unit_trust_leaves(&proof),
        1,
        "only the fixture's own closer survives"
    );

    // The shape the lane promises: ONE `assume` of the authored root, one
    // `and_pos` per conjunct, exactly one `and_neg`.
    assert_eq!(assume_count(&proof), 1, "exactly one assume: the root");
    assert!(
        proof
            .steps
            .iter()
            .any(|step| matches!(step, ProofStep::Assume(term) if *term == root)),
        "and it is the AUTHORED root"
    );
    assert_eq!(count_rule(&proof, &AletheRule::AndNeg), 1);
    let and_pos = proof
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
    assert_eq!(and_pos, 3, "one `and_pos` per conjunct of the root");

    // The last step of the fragment carries the leaf's clause byte for byte.
    assert!(
        proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::Step { rule: AletheRule::ThResolution, clause, .. }
                if clause.as_slice() == [atom]
        )),
        "the fragment must end on exactly the leaf's clause"
    );

    // The whole rewritten proof is accepted by the checker's own fresh
    // definition registry against the authored scope.
    let scope = exec.complete_problem_assertions_for_strict_proof();
    ay_proof::FreshDefRegistry::collect(&proof, &exec.ctx.terms, Some(&scope))
        .expect("the minted definition must satisfy the checker's own registry");
}

/// The `and_neg` step the lane writes is the one the CHECKER validates: its
/// clause is the conjunction plus the syntactic complement of every conjunct,
/// and the complement of a `not`-headed conjunct is the POSITIVE atom (a
/// `TermStore` cannot build `(not (not x))`).
#[test]
fn the_and_neg_clause_is_the_conjunction_plus_every_syntactic_complement() {
    let mut exec = solve(CONJUNCTS);
    let (atom, _, _) = purified_leaf(&mut exec);
    let mut proof = leaf_proof(&mut exec, atom);
    assert_eq!(rerun(&mut exec, &mut proof), 1);

    let conjuncts = conjuncts_of(&exec, atom);
    let expected: Vec<TermId> = std::iter::once(atom)
        .chain(
            conjuncts
                .iter()
                .map(|&conjunct| complement(&mut exec, conjunct)),
        )
        .collect();
    let found = proof
        .steps
        .iter()
        .find_map(|step| match step {
            ProofStep::Step {
                rule: AletheRule::AndNeg,
                clause,
                args,
                ..
            } => Some((clause.clone(), args.clone())),
            _ => None,
        })
        .expect("the lane must have written an and_neg step");
    assert_eq!(found.0, expected, "and_neg clause");
    assert_eq!(found.1, vec![atom], "and_neg names its source term");

    // At least one conjunct is `not`-headed, and its complement is the
    // POSITIVE atom — the case the whole class turns on.
    let negated = conjuncts
        .iter()
        .copied()
        .find(|&c| matches!(exec.ctx.terms.get(c), TermData::Not(_)))
        .expect("the fixture must carry a `not`-headed conjunct");
    let TermData::Not(inner) = exec.ctx.terms.get(negated) else {
        unreachable!()
    };
    let inner = *inner;
    assert_eq!(complement(&mut exec, negated), inner);
}

/// A leaf whose conjuncts are ALL unchanged is not this lane's: it is the
/// authored root itself, and rewriting it would replace one `trust` step with a
/// longer proof that says exactly the same thing (Guard 4).
#[test]
fn a_leaf_identical_to_its_root_is_declined() {
    let mut exec = solve(CONJUNCTS);
    let root = authored_and_root(&exec);
    let mut proof = leaf_proof(&mut exec, root);
    let before = shape(&proof);
    assert_eq!(rerun(&mut exec, &mut proof), 0);
    assert_eq!(shape(&proof), before);
}

/// THE WIRE. The exported document is pinned as exact text, so a printer
/// change cannot silently alter what this lane publishes.
///
/// Two things this pins that are NOT obvious, both measured here:
///
///  1. The printer does not emit the lane's `and_neg` clause verbatim. Alethe's
///     `and_neg` is `(cl (and t_1..t_n) (not t_1) .. (not t_n))` — LITERALLY one
///     `not` per conjunct — and `TermStore` cannot represent `(not (not x))` at
///     all, which is why the lane's own complement of a `not`-headed conjunct is
///     the positive atom. The printer therefore emits the SPEC form `t23a` and
///     bridges it to the lane's clause with one `not_not` step and one
///     `resolution`. That bridge is the printer's, not this lane's, and the
///     strict checker validated the lane's form before it was ever written.
///  2. The minted definition prints TWICE, once per conjunct congruence that
///     cites it, because each cited hypothesis is emitted as a COPY rather than
///     a backward premise reference (the sibling bridge's rule, for the reason
///     its module docs give). `FreshDefRegistry` reads both copies, finds the
///     same definiens for the same symbol, and accepts — SINGLE DEFINIENS is a
///     condition on the definiens, not on the step count.
#[test]
fn the_fragment_prints_one_and_neg_and_no_trust() {
    let mut exec = solve(CONJUNCTS);
    let (atom, _, _) = purified_leaf(&mut exec);
    let mut proof = leaf_proof(&mut exec, atom);
    assert_eq!(rerun(&mut exec, &mut proof), 1);
    let document =
        ay_proof::try_export_alethe(&proof, &exec.ctx.terms).expect("the proof must render");

    assert_eq!(
        document.matches(":rule trust").count(),
        0,
        "no trust step may reach the wire:\n{document}"
    );
    assert_eq!(
        document.matches(":rule and_neg").count(),
        1,
        "exactly one and_neg:\n{document}"
    );
    assert_eq!(
        document.matches(":rule and_pos").count(),
        3,
        "one and_pos per conjunct of the root:\n{document}"
    );
    assert_eq!(
        document.matches("(assume ").count(),
        1,
        "the authored root is the ONLY assume:\n{document}"
    );
    assert!(
        document.contains("(assume t0 (and (ff (and g h) k) (not (ff (and g h) m)) (ff k m)))"),
        "and it is the authored root itself:\n{document}"
    );
    assert_eq!(
        document.matches(":rule hole").count(),
        3,
        "the minted definition once per citing congruence, plus the fixture's \
         own closer:\n{document}"
    );
    assert_eq!(
        document.matches("(cl (= (and g h) pp)) :rule hole").count(),
        2,
        "the minted definition is COPIED per citation, not referenced:\n{document}"
    );
    assert!(
        document.contains(":rule eq_congruent"),
        "the per-conjunct congruence prints under its own name:\n{document}"
    );
    assert!(
        document.contains(
            "(step t8 (cl (not (= (ff (and g h) k) (ff pp k))) \
             (not (ff (and g h) k)) (ff pp k)) :rule equiv_pos2)"
        ),
        "the App-position conjunct bridges with equiv_pos2:\n{document}"
    );
    assert!(
        document.contains(
            "(step t18 (cl (not (= (ff (and g h) m) (ff pp m))) \
             (ff (and g h) m) (not (ff pp m))) :rule equiv_pos1)"
        ),
        "and the conjunct UNDER THE NOT bridges with equiv_pos1 over the LIFTED \
         equality `(= (ff (and g h) m) (ff pp m))` — no `not` congruence \
         anywhere:\n{document}"
    );
    // The exact `and_neg` line, operand for operand, in the SPEC form.
    assert!(
        document.contains(
            "(step t23a (cl (and (ff pp k) (not (ff pp m)) (ff k m)) (not (ff pp k)) \
             (not (not (ff pp m))) (not (ff k m))) :rule and_neg)"
        ),
        "the whole document is:\n{document}"
    );
    assert!(
        document.contains("(step t23b0 (cl (not (not (not (ff pp m)))) (ff pp m)) :rule not_not)"),
        "the printer's own double-negation bridge:\n{document}"
    );
    assert!(
        document.contains(
            "(step t24 (cl (and (ff pp k) (not (ff pp m)) (ff k m))) :rule th_resolution \
             :premises (t23 t10 t20 t22))"
        ),
        "the fragment ends on exactly the leaf's clause, resolved against one \
         derived unit per conjunct:\n{document}"
    );
}

/// The lane is IDEMPOTENT and does not compete with itself: run twice, the
/// second call finds no candidate and leaves the proof byte-identical.
#[test]
fn a_second_run_finds_nothing_and_changes_nothing() {
    let mut exec = solve(CONJUNCTS);
    let (atom, _, _) = purified_leaf(&mut exec);
    let mut proof = leaf_proof(&mut exec, atom);
    assert_eq!(rerun(&mut exec, &mut proof), 1);
    let after = shape(&proof);
    assert_eq!(rerun(&mut exec, &mut proof), 0);
    assert_eq!(shape(&proof), after);
}
