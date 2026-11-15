// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! A library of binary definitions over a boxed sort that the goal never uses.
//!
//! Program verifiers box every value into one uninterpreted sort and ship a
//! library of definitions with each query: `(op x y) = body`, pattern
//! `(op x y)`, both binders of the boxed sort. A query that applies none of
//! them gives trigger matching nothing to instantiate.
//!
//! The diagonal-instance pass used to instantiate every such definition at
//! `x = y = c` for every boxed ground term `c` all the same, because the
//! binder sort is uninterpreted. Each instance minted `(op c c)` and the
//! clipped sums and differences of its body, which the range and arithmetic
//! axioms then matched: several times the instances of the goal itself, all
//! about terms the goal does not mention. The ground solver then spent its
//! rounds on the atoms of those instances. The stalled queries this was
//! reduced from gave no answer in 60 CPU seconds where z3 needs 0.02; the
//! library query below took 321 instances where it now takes 33.
//!
//! Such a query comes with `(set-option :smt.mbqi false)`: instantiate
//! through the triggers only. On that request the pass now leaves a patterned
//! definition alone, whether the ground problem applies its function or not:
//! where it does, the pattern matches and trigger matching supplies the
//! instance.
//!
//! That holds for a definition asserted by itself, as a library ships it. A
//! patterned universal that is part of a larger assertion, the hypothesis of
//! a goal, keeps its instances: there is one of those per goal, not a
//! library, and refutations rest on them.
//!
//! An input without the option keeps the pass as it was. There the instance
//! at `(c, c)` of a definition is often one no trigger leads to, and small
//! formulas are decided by it; the last tests pin two.

use ntest::timeout;

/// Binary definitions in the library.
const OPS: usize = 12;
/// Boxed values in the goal.
const VALUES: usize = 12;

/// The library and a goal over a chain of clipped increments.
/// `first_bound` bounds the first value; `goal` is the last assertion.
fn query(first_bound: u32, goal: &str) -> String {
    let mut smt = String::from(
        r#"
        (set-option :smt.mbqi false)
        (declare-sort Box 0)
        (declare-fun box (Int) Box)
        (declare-fun unbox (Box) Int)
        (assert (forall ((x Int)) (! (= x (unbox (box x))) :pattern ((box x)))))
        (declare-fun hi (Int) Int)
        (assert (= (hi 8) 256))
        (declare-fun clip (Int Int) Int)
        (assert (forall ((b Int) (i Int))
            (! (and (<= 0 (clip b i)) (< (clip b i) (hi b))) :pattern ((clip b i)))))
        (assert (forall ((b Int) (i Int))
            (! (=> (and (<= 0 i) (< i (hi b))) (= i (clip b i))) :pattern ((clip b i)))))
        (declare-fun add (Int Int) Int)
        (assert (forall ((x Int) (y Int)) (! (= (add x y) (+ x y)) :pattern ((add x y)))))
        (declare-fun sub (Int Int) Int)
        (assert (forall ((x Int) (y Int)) (! (= (sub x y) (- x y)) :pattern ((sub x y)))))
        "#,
    );
    for k in 0..OPS {
        smt.push_str(&format!("(declare-fun op{k} (Box Box) Int)\n"));
        let body = if k % 2 == 0 {
            format!(
                "(ite (> (add (unbox x) (unbox y)) {}) \
                 (clip 8 (sub (add (unbox x) (unbox y)) 256)) \
                 (clip 8 (add (unbox x) (unbox y))))",
                255 - k
            )
        } else {
            format!(
                "(ite (< (sub (unbox x) (unbox y)) {k}) \
                 (clip 8 (add (sub (unbox x) (unbox y)) 256)) \
                 (clip 8 (sub (unbox x) (unbox y))))"
            )
        };
        smt.push_str(&format!(
            "(assert (forall ((x Box) (y Box)) (! (= (op{k} x y) {body}) :pattern ((op{k} x y)))))\n"
        ));
    }
    for i in 0..VALUES {
        smt.push_str(&format!(
            "(declare-const v{i} Box)\n\
             (assert (and (<= 0 (unbox v{i})) (< (unbox v{i}) 256)))\n"
        ));
    }
    for i in 0..VALUES - 1 {
        let bound = if i == 0 { first_bound } else { 200 };
        smt.push_str(&format!(
            "(assert (= (unbox v{}) (clip 8 (add (unbox v{i}) 1))))\n\
             (assert (< (unbox v{i}) {bound}))\n",
            i + 1
        ));
    }
    smt.push_str(goal);
    smt.push_str("\n(check-sat)\n");
    smt
}

/// The goal's negation: the last value is not the first plus the chain length.
fn refuted_goal() -> String {
    format!(
        "(assert (not (= (unbox v{}) (+ (unbox v0) {}))))",
        VALUES - 1,
        VALUES - 1
    )
}

fn run(smt: &str) -> (Vec<String>, u64) {
    let commands = ay_frontend::parse(smt).expect("valid SMT-LIB input");
    let mut exec = ay_dpll::Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");
    let instances = exec
        .statistics()
        .get_int("ematching_instances_created")
        .unwrap_or(0);
    (outputs, instances)
}

/// No increment can wrap, so the last value is the first plus the chain
/// length (z3: unsat). Every instance is one of the goal's own `clip` and
/// `add` terms; the library contributes none.
#[test]
#[timeout(120_000)]
fn an_unused_library_adds_no_instances_to_the_refutation() {
    let (outputs, instances) = run(&query(200, &refuted_goal()));
    assert_eq!(outputs, vec!["unsat"]);
    // Two axioms on each of the goal's `clip` terms and one on each `add`.
    let bound = 4 * VALUES as u64;
    assert!(
        instances <= bound,
        "{instances} E-matching instances, bound {bound}: the library was instantiated"
    );
}

/// One binary definition over an uninterpreted sort, an axiom on the function
/// its body applies, and two ground comparisons that contradict each other,
/// from an input that asked for triggers only. Nothing applies `f`, so no
/// pattern has a ground match (z3: unsat with no instance). The pass used to
/// mint `(f a a)` and `(f b b)` here.
const ONE_DEFINITION: &str = r#"
    (set-option :smt.mbqi false)
    (declare-sort U 0)
    (declare-fun f (U U) U)
    (declare-fun h (U) Int)
    (declare-fun k (Int) Int)
    (declare-const a U)
    (declare-const b U)
    (assert (forall ((x U) (y U))
        (! (= (h (f x y)) (k (+ (h x) (h y)))) :pattern ((f x y)))))
    (assert (forall ((i Int)) (! (>= (k i) i) :pattern ((k i)))))
    (assert (< (h a) (h b)))
    (assert (< (h b) (h a)))
    (check-sat)
"#;

#[test]
#[timeout(60_000)]
fn a_definition_nothing_applies_is_not_instantiated() {
    let (outputs, instances) = run(ONE_DEFINITION);
    assert_eq!(outputs, vec!["unsat"]);
    assert_eq!(instances, 0, "no pattern has a ground match");
}

/// The twin differs in one line: its goal applies `f`. The definition is
/// reached and instantiated, and the query has a model (`U` the integers, `h`
/// and `k` the identity, `f` addition, `a = -2`, `b = -1`), so it must not be
/// refuted (z3 with MBQI off: unknown).
#[test]
#[timeout(60_000)]
fn the_twin_whose_goal_applies_the_function_is_not_refuted() {
    let twin = ONE_DEFINITION.replace("(assert (< (h b) (h a)))", "(assert (< (h (f a b)) (h a)))");
    assert_ne!(twin, ONE_DEFINITION);
    let (outputs, instances) = run(&twin);
    assert_eq!(outputs.len(), 1);
    assert_ne!(outputs[0], "unsat", "the twin is satisfiable");
    assert!(instances > 0, "`(f a b)` matches the definition's pattern");
}

/// A formula only the diagonal instance of an unreached definition refutes,
/// from an input that leaves model-based instantiation on. At `x = y = d` the
/// body says `h (f d d) = 2 * (h d)` and `h d > h (f d d)`, so `h d < 0`,
/// against the ground fact; nothing applies `f`, so the pattern has no match
/// (z3: unsat).
const REFUTED_AT_THE_DIAGONAL: &str = r#"
    (declare-sort U 0)
    (declare-fun f (U U) U)
    (declare-fun h (U) Int)
    (declare-const d U)
    (assert (forall ((x U) (y U))
        (! (and (= (h (f x y)) (+ (h x) (h y))) (> (h x) (h (f x x))))
           :pattern ((f x y)))))
    (assert (> (h d) 0))
    (check-sat)
"#;

#[test]
#[timeout(60_000)]
fn a_definition_nothing_applies_is_still_refuted_at_the_diagonal() {
    let (outputs, _) = run(REFUTED_AT_THE_DIAGONAL);
    assert_eq!(outputs, vec!["unsat"]);
}

/// The twin differs in one line: the ground fact is `h d < 0`, which is what
/// the definition forces. It has a model (`U` the negative integers, `h` the
/// identity, `f` addition), so it must not be refuted.
#[test]
#[timeout(60_000)]
fn the_twin_the_diagonal_instance_agrees_with_is_not_refuted() {
    let twin = REFUTED_AT_THE_DIAGONAL.replace("(assert (> (h d) 0))", "(assert (< (h d) 0))");
    assert_ne!(twin, REFUTED_AT_THE_DIAGONAL);
    let (outputs, _) = run(&twin);
    assert_eq!(outputs.len(), 1);
    assert_ne!(outputs[0], "unsat", "the twin is satisfiable");
}

/// The same formula from an input that asked for triggers only. The
/// definition gets no instance, as with z3 under the option (which answers
/// `unknown` once `auto_config` is off as well). The formula has no model, so
/// the answer is never `sat`.
#[test]
#[timeout(60_000)]
fn the_same_formula_under_triggers_only_gets_no_instance() {
    let input = format!("(set-option :smt.mbqi false){REFUTED_AT_THE_DIAGONAL}");
    let (outputs, instances) = run(&input);
    assert_eq!(outputs.len(), 1);
    assert_ne!(outputs[0], "sat", "the formula has no model");
    assert_eq!(instances, 0, "nothing applies `f`, and the pass mints none");
}

/// The same definition as the hypothesis of a goal, under triggers only:
/// `(not (=> hypothesis (<= (h d) 0)))`. The universal is part of a larger
/// assertion, so the pass keeps it, and the instance at `(d, d)` gives the
/// goal (z3 with the option: unsat).
const HYPOTHESIS_REFUTED_AT_THE_DIAGONAL: &str = r#"
    (set-option :smt.mbqi false)
    (declare-sort U 0)
    (declare-fun f (U U) U)
    (declare-fun h (U) Int)
    (declare-const d U)
    (assert (not (=>
        (forall ((x U) (y U))
            (! (and (= (h (f x y)) (+ (h x) (h y))) (> (h x) (h (f x x))))
               :pattern ((f x y))))
        (<= (h d) 0))))
    (check-sat)
"#;

#[test]
#[timeout(60_000)]
fn a_hypothesis_inside_the_goal_keeps_its_diagonal_instance_under_triggers_only() {
    let (outputs, instances) = run(HYPOTHESIS_REFUTED_AT_THE_DIAGONAL);
    assert_eq!(outputs, vec!["unsat"]);
    assert!(instances > 0, "the hypothesis was instantiated");
}

/// The twin differs in one line: the goal is `h d >= 0`, which the
/// hypothesis contradicts, so its negation has a model (`U` the negative
/// integers, `h` the identity, `f` addition) and must not be refuted.
#[test]
#[timeout(60_000)]
fn the_twin_whose_goal_the_hypothesis_contradicts_is_not_refuted() {
    let twin = HYPOTHESIS_REFUTED_AT_THE_DIAGONAL.replace("(<= (h d) 0))))", "(>= (h d) 0))))");
    assert_ne!(twin, HYPOTHESIS_REFUTED_AT_THE_DIAGONAL);
    let (outputs, _) = run(&twin);
    assert_eq!(outputs.len(), 1);
    assert_ne!(outputs[0], "unsat", "the twin is satisfiable");
}

/// A definition the ground problem does reach: `(f d e)` matches the pattern.
/// The refutation needs the self-pair all the same: at `x = y = d` the
/// premise `(f d d) = (f d d)` holds, so `q d`, against the last assertion.
/// Matching gives the instances at `(d, e)` and `(e, d)` only (z3: unsat).
const REACHED_AND_REFUTED_AT_THE_DIAGONAL: &str = r#"
    (declare-sort U 0)
    (declare-fun f (U U) U)
    (declare-fun q (U) Bool)
    (declare-const d U)
    (declare-const e U)
    (assert (forall ((x U) (y U))
        (! (=> (= (f x y) (f y x)) (q x)) :pattern ((f x y)))))
    (assert (= (f d e) e))
    (assert (not (q d)))
    (check-sat)
"#;

#[test]
#[timeout(60_000)]
fn a_definition_the_goal_applies_is_still_refuted_at_the_diagonal() {
    let (outputs, _) = run(REACHED_AND_REFUTED_AT_THE_DIAGONAL);
    assert_eq!(outputs, vec!["unsat"]);
}

/// The twin differs in one line: the ground fact is `q d`. It has a model
/// (`q` true everywhere), so it must not be refuted.
#[test]
#[timeout(60_000)]
fn the_twin_that_asserts_what_the_diagonal_gives_is_not_refuted() {
    let twin =
        REACHED_AND_REFUTED_AT_THE_DIAGONAL.replace("(assert (not (q d)))", "(assert (q d))");
    assert_ne!(twin, REACHED_AND_REFUTED_AT_THE_DIAGONAL);
    let (outputs, _) = run(&twin);
    assert_eq!(outputs.len(), 1);
    assert_ne!(outputs[0], "unsat", "the twin is satisfiable");
}

/// The same formula under triggers only: the definition gets the instances
/// its pattern matches and no diagonal ones on top, as with z3 under the
/// option (which answers `unknown` once `auto_config` is off as well).
#[test]
#[timeout(60_000)]
fn the_reached_definition_under_triggers_only_gets_its_matched_instances_only() {
    let (_, with_diagonal) = run(REACHED_AND_REFUTED_AT_THE_DIAGONAL);
    let input = format!("(set-option :smt.mbqi false){REACHED_AND_REFUTED_AT_THE_DIAGONAL}");
    let (outputs, matched) = run(&input);
    assert_eq!(outputs.len(), 1);
    assert_ne!(outputs[0], "sat", "the formula has no model");
    assert!(matched > 0, "`(f d e)` matches the pattern");
    assert!(
        matched < with_diagonal,
        "{matched} instances under triggers only, {with_diagonal} without the option"
    );
}
