// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! (#defn-fold-binder-capture) The certificate replay's source fold, and the
//! public verdicts that fold and its producer twin feed.
//!
//! A constant registered AFTER a universal can be spelled like the binder the
//! frontend minted for it, and is a different variable. Folding a definition
//! that mentions it under the binder let the expander, which substitutes
//! binders by name, read it as the binder. On ad60a0707 a `declare-const`
//! built that state, and every `collide` case below then published the
//! verdict z3 refutes (`sat` sealed by the exact finite-expansion SAT grant,
//! or `unsat`). A `declare-const` of a binder's spelling now takes a private
//! identity, so the fixtures register the constant as a native-API caller
//! does (`Context::register_symbol` over `TermStore::mk_var`). Each twin
//! differs only in the constant's spelling and keeps its decided verdict, so
//! the fold's payoff (#defn-fold-under-forall, #source-derived-replay-bound)
//! is kept.

use super::*;

const TAIL: &str = "(assert (= lens (store ((as const (Array Int Int)) 0) 0 2))) \
     (assert (= w (store ((as const (Array Int Int)) 0) 0 @B@)))";

/// `(forall i) 0 <= i < lens[0] => i = w[0]` with `lens[0] = 2` and `w[0] =
/// @B@`: `@B@` would have to be both `0` and `1` (z3: unsat).
const EQUAL_HEAD: &str = "(set-logic ALL) \
     (declare-const lens (Array Int Int)) \
     (declare-const w (Array Int Int)) \
     (assert (forall ((i Int)) \
       (=> (and (<= 0 i) (< i (select lens 0))) (= i (select w 0)))))";

/// The `distinct` twin: any `@B@` outside `{0, 1}` satisfies it (z3: sat).
const DISTINCT_HEAD: &str = "(set-logic ALL) \
     (declare-const lens (Array Int Int)) \
     (declare-const w (Array Int Int)) \
     (assert (forall ((i Int)) \
       (=> (and (<= 0 i) (< i (select lens 0))) (distinct i (select w 0)))))";

fn load(exec: &mut Executor, source: &str) {
    let commands = ay_frontend::parse(source).expect("fixture parses");
    exec.execute_all(&commands).expect("fixture elaborates");
}

/// Elaborate `head` (its FIRST assertion must be the universal), register an
/// Int constant spelled like that universal's first binder (`collide`) or as
/// `x`, then run `tail` with `@B@` naming it. Returns the executor, `tail`'s
/// output lines, the spelling used and the constant.
fn run(
    head: &str,
    tail: &str,
    collide: bool,
    configure: impl FnOnce(&mut Executor),
) -> (Executor, Vec<String>, String, TermId) {
    let mut exec = Executor::new();
    configure(&mut exec);
    load(&mut exec, head);
    let TermData::Forall(vars, _, _) = exec.ctx.terms.get(exec.ctx.assertions[0]).clone() else {
        panic!("the head's first assertion is the universal");
    };
    let name = if collide {
        vars[0].0.clone()
    } else {
        "x".to_string()
    };
    let constant = exec.ctx.terms.mk_var(name.clone(), Sort::Int);
    exec.ctx.register_symbol(name.clone(), constant, Sort::Int);
    let commands =
        ay_frontend::parse(&tail.replace("@B@", &name)).expect("the fixture's tail parses");
    let output = exec
        .execute_all(&commands)
        .expect("the fixture's tail runs");
    let spelled_alike = exec
        .ctx
        .terms
        .term_ids()
        .filter(|&t| matches!(exec.ctx.terms.get(t), TermData::Var(n, _) if *n == name))
        .count();
    assert!(
        !collide || spelled_alike >= 2,
        "the collision must hold two identities spelled `{name}`"
    );
    (exec, output, name, constant)
}

fn verdicts(head: &str, tail: &str, collide: bool, configure: fn(&mut Executor)) -> Vec<String> {
    let (_, output, _, _) = run(head, tail, collide, configure);
    output
        .into_iter()
        .filter(|line| matches!(line.as_str(), "sat" | "unsat" | "unknown"))
        .collect()
}

fn plain(_: &mut Executor) {}

fn fast(exec: &mut Executor) {
    exec.set_competition_mode(true);
}

fn self_check(exec: &mut Executor) {
    exec.set_self_check(true);
}

const POSTURES: [(&str, fn(&mut Executor)); 3] =
    [("plain", plain), ("fast", fast), ("self-check", self_check)];

/// Every `Var` `term` mentions, by identity.
fn vars_of(terms: &TermStore, term: TermId) -> HashSet<TermId> {
    let mut vars: HashSet<TermId> = HashSet::default();
    let mut seen: HashSet<TermId> = HashSet::default();
    let mut pending = vec![term];
    while let Some(t) = pending.pop() {
        if !seen.insert(t) {
            continue;
        }
        if matches!(terms.get(t), TermData::Var(..)) {
            vars.insert(t);
        }
        pending.extend(terms.children(t));
    }
    vars
}

/// The replay folds `lens` (its bound becomes `2`) and expands, but leaves
/// `w`, whose value spells the binder, unfolded: its expansion reads `w`
/// and never the declared constant. The twin folds both, and its expansion
/// reads the constant instead of `w`. Before the fix the colliding replay
/// read `@B@` as the binder and expanded to instances that hold for every
/// `@B@`, which is what the SAT grant then sealed.
#[test]
fn the_source_replay_never_folds_a_binder_spelling_under_the_binder() {
    for collide in [true, false] {
        let (mut exec, _, _, constant) = run(EQUAL_HEAD, TAIL, collide, plain);
        let source = exec.ctx.assertions.clone();
        let root = source[0];
        let w = exec
            .ctx
            .terms
            .mk_var("w", Sort::array(Sort::Int, Sort::Int));
        let expanded = {
            let _standalone = crate::skolemize::scoped_standalone_finite_domain_replay();
            replay_from_source(&mut exec.ctx.terms, root, &source)
                .expect("the folded `lens` bound makes the universal finite either way")
        };
        let read = vars_of(&exec.ctx.terms, expanded);
        assert!(!contains_quantifier(&exec.ctx.terms, expanded));
        assert_eq!(read.contains(&w), collide, "collide={collide}");
        assert_eq!(read.contains(&constant), !collide, "collide={collide}");
    }
}

/// z3: unsat. Before the fix: `sat` in every posture, sealed by the exact
/// finite-expansion SAT grant.
#[test]
fn a_captured_equality_never_publishes_sat() {
    for (posture, configure) in POSTURES {
        let collided = verdicts(EQUAL_HEAD, &format!("{TAIL} (check-sat)"), true, configure);
        assert_ne!(
            collided,
            vec!["sat"],
            "{posture}: the captured fold decided a z3-unsat query"
        );
        let twin = verdicts(EQUAL_HEAD, &format!("{TAIL} (check-sat)"), false, configure);
        assert_ne!(twin, vec!["sat"], "{posture}: twin");
    }
    let plain_twin = verdicts(EQUAL_HEAD, &format!("{TAIL} (check-sat)"), false, plain);
    assert_eq!(plain_twin, vec!["unsat"], "the twin stays decided");
}

/// z3: sat. Before the fix: `unsat` without proofs.
#[test]
fn a_captured_distinct_never_publishes_unsat() {
    for (posture, configure) in POSTURES {
        let collided = verdicts(
            DISTINCT_HEAD,
            &format!("{TAIL} (check-sat)"),
            true,
            configure,
        );
        assert_ne!(
            collided,
            vec!["unsat"],
            "{posture}: the captured fold refuted a z3-sat query"
        );
    }
    let plain_twin = verdicts(DISTINCT_HEAD, &format!("{TAIL} (check-sat)"), false, plain);
    assert_eq!(plain_twin, vec!["sat"], "the twin stays decided");
}

/// The binder never occurs in the body, so after the fold the declared
/// constant is the ONLY variable spelled like it; `@B@ > 5` makes `w[0] < 2`
/// false (z3: unsat). Before the fix: `sat` in every posture.
#[test]
fn a_capture_under_a_vacuous_binder_never_publishes_sat() {
    let head = "(set-logic ALL) \
         (declare-const lens (Array Int Int)) \
         (declare-const w (Array Int Int)) \
         (assert (forall ((i Int)) \
           (=> (and (<= 0 i) (< i (select lens 0))) (< (select w 0) 2))))";
    let tail = format!("{TAIL} (assert (> @B@ 5)) (check-sat)");
    for (posture, configure) in POSTURES {
        assert_ne!(
            verdicts(head, &tail, true, configure),
            vec!["sat"],
            "{posture}"
        );
        assert_ne!(
            verdicts(head, &tail, false, configure),
            vec!["sat"],
            "{posture}: twin"
        );
    }
}

/// The fold ERASES the binder's own occurrence (`(select z i)` collapses to
/// `0` once `z := (as const .. 0)` folds), leaving the declared constant the
/// only variable spelled like the binder (z3: unsat). Before the fix: `sat`
/// in every posture.
#[test]
fn a_capture_by_a_fold_that_erases_the_binder_never_publishes_sat() {
    let head = "(set-logic ALL) \
         (declare-const lens (Array Int Int)) \
         (declare-const w (Array Int Int)) \
         (declare-const z (Array Int Int)) \
         (assert (forall ((i Int)) \
           (=> (and (<= 0 i) (< i (select lens 0))) (< (select w (select z i)) 2))))";
    let tail = format!(
        "{TAIL} (assert (= z ((as const (Array Int Int)) 0))) (assert (> @B@ 5)) (check-sat)"
    );
    for (posture, configure) in POSTURES {
        assert_ne!(
            verdicts(head, &tail, true, configure),
            vec!["sat"],
            "{posture}"
        );
        assert_ne!(
            verdicts(head, &tail, false, configure),
            vec!["sat"],
            "{posture}: twin"
        );
    }
}

/// The capture reached E-matching too: the folded body read `(distinct i_k
/// i_k)` for the binder `i_k` and the foreign `i_k`, so the instance at
/// `(P 3)` was `false` (z3: sat). Before the fix: `unsat` under
/// `set_competition_mode` (`--rigor fast`).
#[test]
fn a_captured_ematching_instance_never_publishes_unsat() {
    let head = "(set-logic ALL) \
         (declare-fun P (Int) Bool) \
         (declare-const w (Array Int Int)) \
         (declare-const lens (Array Int Int)) \
         (assert (forall ((i Int)) (! (=> (and (P i) (< i (select lens 0))) \
                                          (distinct i (select w 0))) \
                                      :pattern ((P i)))))";
    let tail = "(assert (= lens (store ((as const (Array Int Int)) 0) 0 10))) \
         (assert (= w (store ((as const (Array Int Int)) 0) 0 @B@))) \
         (assert (P 3)) (check-sat)";
    for (posture, configure) in POSTURES {
        assert_ne!(
            verdicts(head, tail, true, configure),
            vec!["unsat"],
            "{posture}"
        );
        assert_ne!(
            verdicts(head, tail, false, configure),
            vec!["unsat"],
            "{posture}: twin"
        );
    }
}

/// The definition arrives as a `check-sat-assuming` literal (z3: unsat).
/// Before the fix: `sat` in every posture.
#[test]
fn a_capture_through_check_sat_assuming_never_publishes_sat() {
    let tail = "(assert (= lens (store ((as const (Array Int Int)) 0) 0 2))) \
         (check-sat-assuming ((= w (store ((as const (Array Int Int)) 0) 0 @B@))))";
    for (posture, configure) in POSTURES {
        assert_ne!(
            verdicts(EQUAL_HEAD, tail, true, configure),
            vec!["sat"],
            "{posture}"
        );
        assert_ne!(
            verdicts(EQUAL_HEAD, tail, false, configure),
            vec!["sat"],
            "{posture}: twin"
        );
    }
}

/// Inside a `push` scope (z3: unsat, then sat once the scope is popped).
/// Before the fix: `sat` for the scoped query in every posture.
#[test]
fn a_capture_inside_a_push_scope_never_publishes_sat() {
    let head = "(set-logic ALL) \
         (declare-const lens (Array Int Int)) \
         (declare-const w (Array Int Int)) \
         (push 1) \
         (assert (forall ((i Int)) \
           (=> (and (<= 0 i) (< i (select lens 0))) (= i (select w 0)))))";
    let tail = format!("{TAIL} (check-sat) (pop 1) (check-sat)");
    for (posture, configure) in POSTURES {
        let collided = verdicts(head, &tail, true, configure);
        assert_eq!(collided.len(), 2, "{posture}: two check-sats");
        assert_ne!(
            collided[0], "sat",
            "{posture}: the scoped query is z3-unsat"
        );
        assert_ne!(
            collided[1], "unsat",
            "{posture}: the popped query is z3-sat"
        );
    }
}
