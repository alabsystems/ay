// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The two-sided EXHAUSTIVE sweep for the MINTED-DEFINITION leaf lane.
//!
//! Split out of `minted_definition_leaf_negative_tests.rs` so each file stays
//! inside the repository's 500-line ceiling. That file owns the INDEPENDENT
//! model enumerator and the four authority negatives; this one drives the box
//! through them.

use ay_core::{AletheRule, ProofStep, Symbol, TermData, TermId};

use super::negative_tests::{eval, models};
use super::tests::{boolvar, ff, leaf_proof, solve};
use crate::Executor;

/// Every substitution the box can name, crossed with every root the box can
/// name. Each ACCEPT is re-checked TWICE by code that shares nothing with the
/// lane: the model enumerator must find the extension CONSERVATIVE (every
/// model of the authored set extends to one satisfying the minted definition),
/// and the checker's own `FreshDefRegistry` must admit the finished proof.
/// The box is asserted to CONTAIN declines, so a lane that accepted everything
/// would fail here.
#[test]
fn every_substitution_in_the_box_is_decided_and_every_accept_is_independently_rechecked() {
    // `X` ranges over the shapes a `purify_bool_args` argument can take; the
    // second argument is held at `k` so the box stays enumerable.
    let alphabet = [
        "(and g h)",
        "(or g h)",
        "(and g (or h k))",
        "(not g)",
        "g",
        "k",
    ];
    let mut accepted = 0usize;
    let mut declined = 0usize;
    for text in alphabet {
        let source = format!(
            "(set-logic QF_UF)\n\
             (declare-fun g () Bool)\n\
             (declare-fun h () Bool)\n\
             (declare-fun k () Bool)\n\
             (declare-fun zz () Bool)\n\
             (declare-fun ff (Bool Bool) Bool)\n\
             (assert (ff {text} k))\n\
             (assert zz)\n\
             (assert (not zz))\n\
             (check-sat)\n"
        );
        let mut exec = solve(&source);
        let root = match exec
            .complete_problem_assertions_for_strict_proof()
            .into_iter()
            .find(|&t| {
                matches!(exec.ctx.terms.get(t),
                    TermData::App(Symbol::Named(name), _) if name == "ff")
            }) {
            Some(root) => root,
            None => continue,
        };
        let TermData::App(_, root_args) = exec.ctx.terms.get(root).clone() else {
            continue;
        };
        let (a, d) = sweep_one_root(&mut exec, root, &root_args, text);
        accepted += a;
        declined += d;
    }
    assert!(accepted >= 6, "the sweep accepted only {accepted}");
    assert!(
        declined >= 3,
        "the box must CONTAIN declines, found {declined}"
    );
}

/// One root's half of the sweep: the fresh symbol substituted at argument 0, at
/// argument 1, and at both, with every ACCEPT re-checked by the independent
/// model enumerator and by the checker's own registry.
///
/// Extracted so the driving test stays inside the repository's function-size
/// ceiling; it is the same body, unchanged.
fn sweep_one_root(
    exec: &mut Executor,
    root: TermId,
    root_args: &[TermId],
    text: &str,
) -> (usize, usize) {
    let mut accepted = 0usize;
    let mut declined = 0usize;
    let pp = boolvar(exec, "pp");
    let k = boolvar(exec, "k");
    // Substitute the fresh symbol at argument 0, at argument 1, and at both.
    for positions in [vec![0usize], vec![1], vec![0, 1]] {
        let mut leaf_args = root_args.to_vec();
        for &position in &positions {
            leaf_args[position] = pp;
        }
        let atom = ff(exec, leaf_args[0], leaf_args[1]);
        if atom == root {
            continue;
        }
        let mut proof = leaf_proof(exec, atom);
        let scope = exec.complete_problem_assertions_for_strict_proof();
        let derived = exec.derive_leaves_over_minted_definitions(&mut proof, &scope);
        if derived == 0 {
            declined += 1;
            continue;
        }
        accepted += 1;
        // INDEPENDENT re-check 1: CONSERVATIVITY. Every model of the
        // authored root must extend to one satisfying the definition the
        // lane wrote, so the extension adds no constraint.
        let minted: Vec<TermId> = proof
            .steps
            .iter()
            .filter_map(|step| match step {
                ProofStep::Step {
                    rule: AletheRule::FreshDefEq,
                    clause,
                    ..
                } => clause.first().copied(),
                _ => None,
            })
            .collect();
        assert_eq!(minted.len(), 1, "one definition per accepted leaf");
        let before = models(&exec.ctx.terms, &[root]);
        let mut extended = vec![root];
        extended.push(minted[0]);
        let after = models(&exec.ctx.terms, &extended);
        assert!(!before.is_empty(), "the authored root must be satisfiable");
        assert!(
            !after.is_empty(),
            "the extension refuted a satisfiable authored set"
        );
        // Every model of the root must survive: projecting the extended
        // models onto the problem's own symbols must recover all of them.
        let g = boolvar(exec, "g");
        let h = boolvar(exec, "h");
        for m in &before {
            let key = (
                eval(&exec.ctx.terms, g, m),
                eval(&exec.ctx.terms, h, m),
                eval(&exec.ctx.terms, k, m),
                m.ff_table(),
            );
            assert!(
                after.iter().any(|n| (
                    eval(&exec.ctx.terms, g, n),
                    eval(&exec.ctx.terms, h, n),
                    eval(&exec.ctx.terms, k, n),
                    n.ff_table(),
                ) == key),
                "a model of the authored root did NOT extend: {text}"
            );
        }
        // INDEPENDENT re-check 2: the checker's own whole-proof registry.
        ay_proof::FreshDefRegistry::collect(&proof, &exec.ctx.terms, Some(&scope))
            .expect("the checker's registry must admit every accepted proof");
        ay_proof::check_proof(&proof, &exec.ctx.terms).expect("the rebuilt proof must replay");
    }
    (accepted, declined)
}
