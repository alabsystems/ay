// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The two-sided EXHAUSTIVE sweep for the AUTHORED-CONJUNCT leaf lane.
//!
//! Split out of `authored_conjunct_leaf_negative_tests.rs` so each file stays
//! inside the repository's 500-line ceiling. That file owns the INDEPENDENT
//! evaluator (`decidable` / `eval` / `falsify`) and the adversarial negatives;
//! this one drives the whole box through them.
//!
//! Every ACCEPT is re-checked twice: by the independent evaluator, which
//! enumerates EVERY assignment and must find no countermodel, and by the
//! UNTOUCHED `check_proof_strict` on the closed fragment. The box is asserted
//! to CONTAIN refutable neighbours, so an evaluator that answered "valid" for
//! everything would fail the test.

use ay_core::{AletheRule, ProofStep, Symbol, TermData, TermId};

use super::negative_tests::{
    authored_root, boolvar, decidable, exact_leaf_proof, falsify, run, scoped,
};
use crate::Executor;

/// One node of the sweep's grammar. `text` and `build` are two renderings of
/// the SAME description; the SEMANTIC verdict comes from [`falsify`], which
/// shares nothing with either.
#[derive(Clone)]
enum Node {
    Atom(usize),
    Not(usize),
    And(Vec<Node>),
    Or(usize, usize),
}

impl Node {
    fn text(&self) -> String {
        match self {
            Self::Atom(i) => format!("b{i}"),
            Self::Not(i) => format!("(not b{i})"),
            Self::And(children) => {
                let inner: Vec<String> = children.iter().map(Self::text).collect();
                format!("(and {})", inner.join(" "))
            }
            Self::Or(i, j) => format!("(or b{i} b{j})"),
        }
    }

    fn build(&self, exec: &mut Executor) -> TermId {
        match self {
            Self::Atom(i) => boolvar(exec, &format!("b{i}")),
            Self::Not(i) => {
                let atom = boolvar(exec, &format!("b{i}"));
                exec.ctx.terms.mk_not(atom)
            }
            Self::And(children) => {
                let built: Vec<TermId> = children.iter().map(|c| c.build(exec)).collect();
                exec.ctx.terms.mk_and(built)
            }
            Self::Or(i, j) => {
                let left = boolvar(exec, &format!("b{i}"));
                let right = boolvar(exec, &format!("b{j}"));
                exec.ctx.terms.mk_or(vec![left, right])
            }
        }
    }
}

fn sweep_alphabet() -> Vec<Node> {
    vec![
        Node::Atom(0),
        Node::Atom(1),
        Node::Not(1),
        Node::And(vec![Node::Atom(2), Node::Atom(3)]),
        Node::Or(2, 3),
    ]
}

#[test]
fn every_nested_conjunct_in_the_box_is_derived_and_every_accept_is_independently_rechecked() {
    let alphabet = sweep_alphabet();
    let mut roots: Vec<Node> = Vec::new();
    for left in &alphabet {
        for right in &alphabet {
            roots.push(Node::And(vec![left.clone(), right.clone()]));
            for third in &alphabet {
                roots.push(Node::And(vec![left.clone(), right.clone(), third.clone()]));
            }
        }
    }
    assert_eq!(
        roots.len(),
        150,
        "the box must be the one the docs describe"
    );

    let mut accepted = 0usize;
    let mut refuted_neighbours = 0usize;
    let mut skipped = 0usize;
    for root_node in &roots {
        let mut exec = scoped(&root_node.text());
        let root = root_node.build(&mut exec);
        if !exec
            .complete_problem_assertions_for_strict_proof()
            .contains(&root)
        {
            // `mk_and` folds (duplicate and `true` conjuncts), so a built root
            // can differ from the parsed assertion. Skipped rather than
            // silently counted; the assertion below bounds how often.
            skipped += 1;
            continue;
        }
        let (a, r) = sweep_one_root(&mut exec, root, root_node, &alphabet);
        accepted += a;
        refuted_neighbours += r;
    }
    assert!(accepted >= 300, "the sweep accepted only {accepted}");
    assert!(
        refuted_neighbours >= 100,
        "the box must CONTAIN refutable neighbours, found {refuted_neighbours}"
    );
    assert!(skipped <= 60, "too many roots were folded away: {skipped}");
}

#[test]
fn the_lane_never_emits_an_and_pos_whose_position_the_checker_refuses() {
    // A direct pin on the emitted `and_pos` position: the checker's own
    // `validate_and_pos` reads `:args` and the position index, so a fragment
    // carrying the WRONG index is refused by Guard 6. Here the position is
    // re-derived from the authored root, independently of the lane.
    let mut exec = scoped("(and b0 (not b1) b2)");
    let root = authored_root(&exec, "and");
    let b1 = boolvar(&mut exec, "b1");
    let goal = exec.ctx.terms.mk_not(b1);
    let (derived, proof) = run(&mut exec, goal);
    assert_eq!(derived, 1);
    let TermData::App(_, args) = exec.ctx.terms.get(root).clone() else {
        panic!("the root is an application");
    };
    let expected = args
        .iter()
        .position(|&arg| arg == goal)
        .expect("the goal is a conjunct of the root");
    let positions: Vec<u32> = proof
        .steps
        .iter()
        .filter_map(|step| match step {
            ProofStep::Step {
                rule: AletheRule::AndPos(position),
                ..
            } => Some(*position),
            _ => None,
        })
        .collect();
    assert_eq!(positions, vec![u32::try_from(expected).expect("small")]);
}

/// One root's half of the sweep: every WANTED conjunct plus every neighbour the
/// alphabet can name, with each ACCEPT re-checked by the independent evaluator
/// and by the untouched strict checker. Returns `(accepts, refuted neighbours)`.
///
/// Extracted so the driving test stays inside the repository's function-size
/// ceiling; it is the same body, unchanged.
fn sweep_one_root(
    exec: &mut Executor,
    root: TermId,
    root_node: &Node,
    alphabet: &[Node],
) -> (usize, usize) {
    let mut accepted = 0usize;
    let mut refuted_neighbours = 0usize;
    // The WANTED set: every nested `and`-conjunct at depth >= 1, computed
    // here by a walk that shares no code with the lane's index.
    let mut wanted: Vec<TermId> = Vec::new();
    let mut stack: Vec<(TermId, usize)> = vec![(root, 0)];
    while let Some((node, depth)) = stack.pop() {
        if depth > 0 && !wanted.contains(&node) {
            wanted.push(node);
        }
        if let TermData::App(Symbol::Named(name), args) = exec.ctx.terms.get(node) {
            if name == "and" {
                for &arg in args.clone().iter() {
                    stack.push((arg, depth + 1));
                }
            }
        }
    }
    // Neighbours: everything else the alphabet can name.
    let mut goals: Vec<(TermId, bool)> = wanted.iter().map(|&term| (term, true)).collect();
    for node in alphabet {
        let term = node.build(exec);
        if !wanted.contains(&term) && term != root {
            goals.push((term, false));
        }
    }

    for (goal, expected) in goals {
        let scope = exec.complete_problem_assertions_for_strict_proof();
        let mut proof = exact_leaf_proof(exec, goal);
        let derived = exec.derive_authored_conjunct_leaves(&mut proof, &scope);
        assert_eq!(
            derived,
            usize::from(expected),
            "root {} goal {:?} expected derived={expected}",
            root_node.text(),
            goal
        );
        if derived == 1 {
            accepted += 1;
            // INDEPENDENT re-check of the ACCEPT: the root must entail the
            // goal under EVERY assignment.
            assert!(
                decidable(&exec.ctx.terms, root) && decidable(&exec.ctx.terms, goal),
                "the evaluator must understand both terms"
            );
            assert!(
                falsify(&exec.ctx.terms, root, goal).is_none(),
                "the lane accepted a goal the root does not entail: {}",
                root_node.text()
            );
            // And the fragment must replay under the untouched checker.
            let fragment: Vec<ProofStep> = proof.steps[..proof.steps.len() - 2].to_vec();
            let closed = ay_proof::close_congruence_derivation(
                &mut exec.ctx.terms,
                &ay_proof::CongruenceDerivation {
                    steps: fragment,
                    clause: vec![goal],
                },
            );
            ay_proof::check_proof_strict(&closed, &exec.ctx.terms)
                .expect("every accepted fragment must strict-check");
        } else if decidable(&exec.ctx.terms, root)
            && decidable(&exec.ctx.terms, goal)
            && falsify(&exec.ctx.terms, root, goal).is_some()
        {
            refuted_neighbours += 1;
        }
    }
    (accepted, refuted_neighbours)
}
