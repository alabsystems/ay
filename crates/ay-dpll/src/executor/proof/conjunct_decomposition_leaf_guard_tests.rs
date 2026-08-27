// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The SHAPE guards of the conjunct-decomposition lane, and the mutation
//! ledger.
//!
//! # GUARD MUTATION LEDGER
//!
//! Each guard was deleted or weakened, `cargo test -p ay-dpll --lib` re-run,
//! the named test observed FAILING, and the guard restored. Run recorded
//! 2026-08-23, one mutation at a time. Every row marked NEGATIVE was ALSO run
//! UNFILTERED over the whole 7 319-test lib before it was written down.
//! `NEGATIVE` rows are results, not omissions.
//!
//! | # | guard | mutation | result |
//! |---|---|---|---|
//! | 1 | no `Anchor` steps | delete the early return | **RED** — `a_proof_carrying_an_anchor_is_left_alone` |
//! | 2a | premiseless / argument-free / unit clause | drop the conjunction | **RED** — `a_trust_step_with_premises_or_args_is_left_alone` |
//! | 2b | the atom is an `and` of >= 2 conjuncts | `>= 2` becomes `>= 1` | **RED** — `the_candidate_predicate_requires_a_conjunction_of_at_least_two`. First run came back GREEN through the lane: an arity-1 `and` has no same-arity AUTHORED root, so Guard 3 declines it anyway. The fixture was re-aimed at the PREDICATE, which is the only place the test is observable |
//! | 3a | the pool is the INTERSECTION of both authored scopes | delete the strict-scope filter in `nonequality_roots` | **RED** — `a_root_only_the_handed_scope_carries_is_never_assumed`. First run came back GREEN because the normal entry point hands the lane the strict scope itself, making the intersection a no-op; the fixture now hands an EXPLICIT scope so the two differ |
//! | 3b | the root has the SAME ARITY | delete the length test | **NEGATIVE** — `nonequality_roots` is keyed by `(head symbol, ARITY)` and the lookup uses the LEAF's arity, so a root of a different arity never reaches the loop. Kept as defence in depth and pinned by `a_root_of_a_different_arity_is_declined`, which asserts the authored root really is arity 3 |
//! | 4 | the `root == atom` skip | delete it | **NEGATIVE** — the minter declines an alignment with NO differing pairs, so a leaf identical to its root is refused one guard later. Pinned by `a_leaf_identical_to_its_root_is_declined`. (The separate conjunct-wise "something differs" test this lane started with was DELETED rather than baselined: `TermStore` hash-conses, so equal argument lists are the same term and the test was provably dead) |
//! | 5a | `align_through_not` descends `Not` | delete the `Not` arm | **RED** — **9 tests**, including `the_alignment_descends_the_not_and_records_the_variable_underneath` and the whole positive path. This is the one line that separates this lane from its sibling |
//! | 5b | FRESH (`constrained.contains`) | delete it | GREEN alone — `commit_bridge_fragments`' `check_proof` runs the checker's OWN `FreshDefRegistry` with `None` problem assertions, which cannot see a definiendum the PROBLEM constrains but no `assume` does |
//! | **5b + 10** | FRESH **and** Gate 2 together | delete BOTH | **RED** — `a_definiendum_the_problem_constrains_is_refused` AND `the_alignment_records_a_non_variable_difference_under_a_not`. This pair is what makes Gate 2 observably load-bearing, and it is the exact case Gate 2 exists for |
//! | 6 | the `equiv_pos` rule is CHOSEN by the checker | return `EquivPos1` unconditionally | **RED** — **8 tests**, headed by `both_equiv_pos_rules_are_used_by_one_fragment`: this population needs `equiv_pos2` for the `App`-position conjunct and `equiv_pos1` for the conjunct under the `not`, so no constant answer serves both |
//! | 7 | the `and_neg` step strict-checks, CLOSED, before it is written | delete the check | **NEGATIVE**, unfiltered: 7 318 passed / 0 failed. The clause is built FROM the conjuncts, so the lane cannot construct a non-tautology, and `commit_bridge_fragments`' whole-proof `check_proof` is the named backstop. Pinned DIRECTLY instead by `a_forged_and_neg_is_refused_by_the_guard_the_lane_uses`, which hands that same closed-derivation check a forged clause, observes the refusal, and NAMES the assignment that falsifies it |
//! | 8 | the fragment ends on exactly the leaf's clause | delete the test | **NEGATIVE**, unfiltered: 7 319 passed / 0 failed. The closing `th_resolution` is CONSTRUCTED with `vec![atom]`, so the postcondition cannot fail without a construction bug — the same unfalsifiable shape the sibling lane records for `descents.is_empty()`. Kept because every consumer of the splice depends on it |
//! | 9 | the fragment RENDERS | return `false` unconditionally | **NEGATIVE**, unfiltered — the sibling lanes carry the same guard and the same finding. Pinned directly by `the_fragment_prints_one_and_neg_and_no_trust`, which exports the document and reads the exact text back |
//! | 10 | GATE 2, the whole-proof `FreshDefRegistry::collect` | delete it ALONE | **NEGATIVE**, unfiltered — backstopped as described in row 5b. RED in the 5b+10 pair |
//!
//! **6 individually RED, plus the 5b+10 PAIR RED; 5 honest negatives**, each
//! with its backstop named and each pinned by a direct test instead. Two of the
//! six REDs only became observable after the fixture was re-aimed away from the
//! lane's derivation COUNT and at the predicate the guard lives in — which is
//! the trap the sibling lane's ledger records, hit again here.

use ay_core::{AletheRule, ProofId, ProofStep, Sort, Symbol, TermData, TermId};

use crate::Executor;

use super::super::minted_definition_leaf::{align, MAX_ALIGN_NODES};
use super::tests::{
    authored_and_root, boolvar, leaf_proof, purified_leaf, rerun, rerun_with_scope, shape, solve,
    substitute, CONJUNCTS,
};
use super::{align_through_not, conjunction_children, is_decomposition_candidate};

/// GUARD 1 — a proof carrying an `Anchor` is left byte-identical.
#[test]
fn a_proof_carrying_an_anchor_is_left_alone() {
    let mut exec = solve(CONJUNCTS);
    let (atom, _, _) = purified_leaf(&mut exec);
    let mut proof = leaf_proof(&mut exec, atom);
    proof.steps.push(ProofStep::Anchor {
        variables: Vec::new(),
        end_step: ProofId(0),
    });
    let before = shape(&proof);
    assert_eq!(rerun(&mut exec, &mut proof), 0);
    assert_eq!(shape(&proof), before);

    // Two-sided: the SAME proof without the anchor is derived.
    let mut clean = leaf_proof(&mut exec, atom);
    assert_eq!(rerun(&mut exec, &mut clean), 1);
}

/// GUARD 2a — a `trust` step with premises, or with args, is not a leaf.
#[test]
fn a_trust_step_with_premises_or_args_is_left_alone() {
    for variant in 0..2 {
        let mut exec = solve(CONJUNCTS);
        let (atom, root, _) = purified_leaf(&mut exec);
        let mut proof = leaf_proof(&mut exec, atom);
        let ProofStep::Step { premises, args, .. } = &mut proof.steps[0] else {
            unreachable!()
        };
        if variant == 0 {
            // A backward premise reference: step 0 has none available, so point
            // the LEAF at a step appended before it.
            premises.push(ProofId(0));
        } else {
            args.push(root);
        }
        let before = shape(&proof);
        assert_eq!(rerun(&mut exec, &mut proof), 0, "variant {variant}");
        assert_eq!(shape(&proof), before, "variant {variant}");
    }
}

/// GUARD 2b — a leaf that is not an `and` of at least two conjuncts belongs to
/// the sibling lanes, and this one never competes for it.
#[test]
fn a_non_conjunction_leaf_is_left_to_the_sibling_lanes() {
    let mut exec = solve(CONJUNCTS);
    let k = boolvar(&mut exec, "k");
    let m = boolvar(&mut exec, "m");
    let plain = exec
        .ctx
        .terms
        .mk_app(Symbol::named("ff"), vec![k, m], Sort::Bool);
    let mut proof = leaf_proof(&mut exec, plain);
    let before = shape(&proof);
    assert_eq!(rerun(&mut exec, &mut proof), 0);
    assert_eq!(shape(&proof), before);

    // A ONE-conjunct `and` is also refused: there is nothing to decompose.
    let unary = exec
        .ctx
        .terms
        .mk_app(Symbol::named("and"), vec![plain], Sort::Bool);
    assert_eq!(
        conjunction_children(&exec.ctx.terms, unary).map(<[TermId]>::len),
        Some(1)
    );
    let mut proof = leaf_proof(&mut exec, unary);
    let before = shape(&proof);
    assert_eq!(rerun(&mut exec, &mut proof), 0);
    assert_eq!(shape(&proof), before);
}

/// GUARD 2b, asked DIRECTLY.
///
/// Through the lane this guard is unobservable: an arity-1 `and` has no
/// same-arity AUTHORED root (`mk_and` collapses a one-element conjunction, so
/// no problem can author one), and Guard 3 declines it anyway. The predicate is
/// therefore asked on its own, which is what makes the `>= 2` test RED under
/// mutation instead of green-and-backstopped.
#[test]
fn the_candidate_predicate_requires_a_conjunction_of_at_least_two() {
    let mut exec = solve(CONJUNCTS);
    let (atom, _, _) = purified_leaf(&mut exec);
    let k = boolvar(&mut exec, "k");
    let m = boolvar(&mut exec, "m");
    let plain = exec
        .ctx
        .terms
        .mk_app(Symbol::named("ff"), vec![k, m], Sort::Bool);
    let unary = exec
        .ctx
        .terms
        .mk_app(Symbol::named("and"), vec![plain], Sort::Bool);
    let binary = exec
        .ctx
        .terms
        .mk_app(Symbol::named("and"), vec![plain, k], Sort::Bool);

    let leaf = |clause: Vec<TermId>, premises: Vec<ProofId>, args: Vec<TermId>| ProofStep::Step {
        rule: AletheRule::Trust,
        clause,
        premises,
        args,
    };
    let candidate =
        |exec: &Executor, step: &ProofStep| is_decomposition_candidate(&exec.ctx.terms, step);

    assert_eq!(
        candidate(&exec, &leaf(vec![atom], Vec::new(), Vec::new())),
        Some(atom),
        "the lane's own population must be a candidate"
    );
    assert_eq!(
        candidate(&exec, &leaf(vec![binary], Vec::new(), Vec::new())),
        Some(binary),
        "two conjuncts is the minimum that CAN be decomposed"
    );
    assert_eq!(
        candidate(&exec, &leaf(vec![unary], Vec::new(), Vec::new())),
        None,
        "a ONE-conjunct `and` has nothing to decompose"
    );
    assert_eq!(
        candidate(&exec, &leaf(vec![plain], Vec::new(), Vec::new())),
        None,
        "a non-conjunction belongs to the sibling lanes"
    );
    assert_eq!(
        candidate(&exec, &leaf(vec![atom], vec![ProofId(0)], Vec::new())),
        None,
        "a trust step WITH premises is a failed derivation, not a leaf"
    );
    assert_eq!(
        candidate(&exec, &leaf(vec![atom], Vec::new(), vec![atom])),
        None,
        "nor is one with arguments"
    );
    assert_eq!(
        candidate(&exec, &leaf(vec![atom, plain], Vec::new(), Vec::new())),
        None,
        "nor a multi-literal clause"
    );
    let not_trust = ProofStep::Step {
        rule: AletheRule::ThResolution,
        clause: vec![atom],
        premises: Vec::new(),
        args: Vec::new(),
    };
    assert_eq!(candidate(&exec, &not_trust), None, "nor a derived step");
}

/// GUARD 3a — a root that is not an authored assertion is NEVER assumed.
///
/// The leaf here is a two-conjunct `and` built out of authored sub-terms; its
/// only same-arity `and` neighbour is a term the problem never asserted, so no
/// root is available and the lane declines. The two-sided half is the positive
/// test, whose root IS in the strict scope.
#[test]
fn a_root_outside_the_authored_scope_is_never_assumed() {
    let mut exec = solve(CONJUNCTS);
    let k = boolvar(&mut exec, "k");
    let m = boolvar(&mut exec, "m");
    let pp = boolvar(&mut exec, "pp");
    let left = exec
        .ctx
        .terms
        .mk_app(Symbol::named("ff"), vec![pp, k], Sort::Bool);
    let right = exec
        .ctx
        .terms
        .mk_app(Symbol::named("ff"), vec![pp, m], Sort::Bool);
    let leaf = exec
        .ctx
        .terms
        .mk_app(Symbol::named("and"), vec![left, right], Sort::Bool);
    let scope = exec.complete_problem_assertions_for_strict_proof();
    assert!(
        !scope.iter().any(|&term| matches!(
            exec.ctx.terms.get(term),
            TermData::App(Symbol::Named(name), args) if name == "and" && args.len() == 2
        )),
        "the fixture must author NO arity-2 `and`, or this proves nothing"
    );
    let mut proof = leaf_proof(&mut exec, leaf);
    let before = shape(&proof);
    assert_eq!(rerun(&mut exec, &mut proof), 0);
    assert_eq!(shape(&proof), before);
}

/// GUARD 3a, made OBSERVABLE: the pool is the INTERSECTION of the scope the
/// rewrite was HANDED and the scope the strict presentation CHECKS against, and
/// a root that only the handed scope carries must never be assumed.
///
/// Through the normal entry point the two scopes are the same set, so the
/// intersection is a no-op and the guard is invisible (measured: deleting the
/// strict-scope filter fails nothing there). This test hands the lane a scope
/// containing a root the problem never asserted — `(and A B (ff m k))`, whose
/// third conjunct has its arguments swapped — and requires a decline.
#[test]
fn a_root_only_the_handed_scope_carries_is_never_assumed() {
    let mut exec = solve(CONJUNCTS);
    let root = authored_and_root(&exec);
    let conjuncts = conjunction_children(&exec.ctx.terms, root)
        .expect("the root is an `and`")
        .to_vec();
    let k = boolvar(&mut exec, "k");
    let m = boolvar(&mut exec, "m");
    let swapped = exec
        .ctx
        .terms
        .mk_app(Symbol::named("ff"), vec![m, k], Sort::Bool);
    let foreign = exec.ctx.terms.mk_app(
        Symbol::named("and"),
        vec![conjuncts[0], conjuncts[1], swapped],
        Sort::Bool,
    );
    let strict = exec.complete_problem_assertions_for_strict_proof();
    assert!(
        !strict.contains(&foreign),
        "the fixture's foreign root must NOT be authored"
    );
    let g = boolvar(&mut exec, "g");
    let h = boolvar(&mut exec, "h");
    let definiens = exec.ctx.terms.mk_and(vec![g, h]);
    let pp = boolvar(&mut exec, "pp");
    let leaf = substitute(&mut exec, foreign, definiens, pp);
    assert_ne!(leaf, foreign);

    let mut proof = leaf_proof(&mut exec, leaf);
    let before = shape(&proof);
    assert_eq!(
        rerun_with_scope(&mut exec, &mut proof, &[foreign]),
        0,
        "a root only the HANDED scope carries must never be assumed"
    );
    assert_eq!(shape(&proof), before);

    // Two-sided: the same entry point, handed the AUTHORED root, DOES derive
    // the leaf aligned to it — so the decline above is about the scope and not
    // about the entry point.
    let (authored_leaf, authored_root, _) = purified_leaf(&mut exec);
    let mut ok = leaf_proof(&mut exec, authored_leaf);
    assert_eq!(rerun_with_scope(&mut exec, &mut ok, &[authored_root]), 1);
}

/// GUARD 3b — the root must have the SAME ARITY. A three-conjunct root cannot
/// explain a two-conjunct leaf, and pairing them index by index would silently
/// drop a conjunct.
#[test]
fn a_root_of_a_different_arity_is_declined() {
    let mut exec = solve(CONJUNCTS);
    let (atom, root, _) = purified_leaf(&mut exec);
    let conjuncts = conjunction_children(&exec.ctx.terms, atom)
        .expect("the leaf is an `and`")
        .to_vec();
    assert_eq!(conjuncts.len(), 3);
    let truncated = exec.ctx.terms.mk_app(
        Symbol::named("and"),
        vec![conjuncts[0], conjuncts[1]],
        Sort::Bool,
    );
    // The authored root really is arity 3, so the arity test is what refuses it.
    assert_eq!(
        conjunction_children(&exec.ctx.terms, root).map(<[TermId]>::len),
        Some(3)
    );
    let mut proof = leaf_proof(&mut exec, truncated);
    let before = shape(&proof);
    assert_eq!(rerun(&mut exec, &mut proof), 0);
    assert_eq!(shape(&proof), before);
}

/// GUARD 5a — the alignment DESCENDS the `not`, and that is the one difference
/// from the sibling lane's alignment.
///
/// Two-sided and asked DIRECTLY, because both alignments are backstopped when
/// asked through the lane: the sibling's `align` records the whole `Not` NODE
/// pair (whose leaf side is not a variable, so the mint declines), and this
/// lane's records the fresh VARIABLE underneath it.
#[test]
fn the_alignment_descends_the_not_and_records_the_variable_underneath() {
    let mut exec = solve(CONJUNCTS);
    let (atom, root, pp) = purified_leaf(&mut exec);
    let g = boolvar(&mut exec, "g");
    let h = boolvar(&mut exec, "h");
    let definiens = exec.ctx.terms.mk_and(vec![g, h]);

    let mut through: Vec<(TermId, TermId)> = Vec::new();
    let mut budget = MAX_ALIGN_NODES;
    assert!(align_through_not(
        &exec.ctx.terms,
        atom,
        root,
        &mut through,
        &mut budget
    ));
    assert!(
        through
            .iter()
            .all(|&(leaf, rooted)| leaf == pp && rooted == definiens),
        "every differing position must be the fresh variable and its definiens: \
         {through:?}"
    );
    assert_eq!(
        through.len(),
        2,
        "one per occurrence of the compound argument"
    );

    let mut stopping: Vec<(TermId, TermId)> = Vec::new();
    let mut budget = MAX_ALIGN_NODES;
    assert!(align(
        &exec.ctx.terms,
        atom,
        root,
        &mut stopping,
        &mut budget
    ));
    assert!(
        stopping
            .iter()
            .any(|&(leaf, _)| matches!(exec.ctx.terms.get(leaf), TermData::Not(_))),
        "the sibling alignment must STOP at the `not` and record the whole node: \
         {stopping:?}"
    );
    assert!(
        !stopping.iter().all(|&(leaf, _)| leaf == pp),
        "which is exactly why the whole-term lane declines this leaf"
    );

    // And the budget is honoured: a zero budget refuses rather than recursing.
    let mut out: Vec<(TermId, TermId)> = Vec::new();
    let mut none = 0usize;
    assert!(!align_through_not(
        &exec.ctx.terms,
        atom,
        root,
        &mut out,
        &mut none
    ));
}

/// GUARD 5a, the other side: a `not` whose INSIDE is not congruent is still
/// recorded as a differing pair rather than silently accepted.
#[test]
fn the_alignment_records_a_non_variable_difference_under_a_not() {
    let mut exec = solve(CONJUNCTS);
    let root = authored_and_root(&exec);
    let k = boolvar(&mut exec, "k");
    let m = boolvar(&mut exec, "m");
    let leaf = substitute(&mut exec, root, k, m);
    assert_ne!(leaf, root);
    let mut out: Vec<(TermId, TermId)> = Vec::new();
    let mut budget = MAX_ALIGN_NODES;
    assert!(align_through_not(
        &exec.ctx.terms,
        leaf,
        root,
        &mut out,
        &mut budget
    ));
    assert!(
        out.iter().any(|&(left, right)| left == m && right == k),
        "the differing position must be recorded: {out:?}"
    );
    // And it is NOT a fresh variable, so the lane declines the leaf outright.
    let mut proof = leaf_proof(&mut exec, leaf);
    let before = shape(&proof);
    assert_eq!(rerun(&mut exec, &mut proof), 0);
    assert_eq!(shape(&proof), before);
}

/// GUARD 6 — the `equiv_pos` rule is chosen by the CHECKER, and this population
/// needs BOTH: `equiv_pos2` for the `App`-position conjunct and `equiv_pos1`
/// for the conjunct under the `not`. A constant answer cannot serve both.
#[test]
fn both_equiv_pos_rules_are_used_by_one_fragment() {
    let mut exec = solve(CONJUNCTS);
    let (atom, _, _) = purified_leaf(&mut exec);
    let mut proof = leaf_proof(&mut exec, atom);
    assert_eq!(rerun(&mut exec, &mut proof), 1);
    let count = |wanted: &AletheRule| {
        proof
            .steps
            .iter()
            .filter(|step| matches!(step, ProofStep::Step { rule, .. } if rule == wanted))
            .count()
    };
    assert_eq!(
        count(&AletheRule::EquivPos1),
        1,
        "the conjunct under the not"
    );
    assert_eq!(
        count(&AletheRule::EquivPos2),
        1,
        "the App-position conjunct"
    );
}

/// The lane never widens an authority: the ONLY `assume` any fragment writes is
/// the authored root, and every other step is a tautology or a resolution.
#[test]
fn the_only_assume_is_the_authored_root() {
    let mut exec = solve(CONJUNCTS);
    let (atom, root, _) = purified_leaf(&mut exec);
    let mut proof = leaf_proof(&mut exec, atom);
    assert_eq!(rerun(&mut exec, &mut proof), 1);
    let scope = exec.complete_problem_assertions_for_strict_proof();
    for step in &proof.steps {
        if let ProofStep::Assume(term) = step {
            assert_eq!(*term, root, "no assume but the authored root");
            assert!(scope.contains(term), "and it is in the strict scope");
        }
    }
    let rules: Vec<String> = proof
        .steps
        .iter()
        .filter_map(|step| match step {
            ProofStep::Step { rule, .. } => Some(format!("{rule:?}")),
            _ => None,
        })
        .collect();
    for rule in &rules {
        assert!(
            matches!(
                rule.as_str(),
                "AndPos(0)"
                    | "AndPos(1)"
                    | "AndPos(2)"
                    | "AndNeg"
                    | "ThResolution"
                    | "Resolution"
                    | "EqCongruent"
                    | "EqReflexive"
                    | "EqTransitive"
                    | "EquivPos1"
                    | "EquivPos2"
                    | "FreshDefEq"
                    | "Trust"
                    | "Weakening"
                    | "Reordering"
                    | "Contraction"
            ),
            "unexpected rule in the fragment: {rule}"
        );
    }
}
