// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Which universals the diagonal-instance pass takes.
//!
//! The pass instantiates universals over two or more same-sort variables at
//! `x = y = c` for every ground term `c` of that sort. It takes universals
//! whose body applies no function to their binders, whatever their patterns,
//! and universals over an uninterpreted sort. When the input asked for
//! instantiation through triggers only (`smt.mbqi false`), it leaves out the
//! universals over an uninterpreted sort that carry a pattern and are
//! asserted by themselves: those are instantiated where the pattern matches.
//! A patterned universal that is part of a larger assertion, a hypothesis
//! inside a goal, keeps its instances.

use super::check_sat_output;
use crate::Executor;
use ay_frontend::parse;

/// The answer and the number of E-matching instances of a one-query script.
fn answer_and_instances(smt: &str) -> (String, u64) {
    let commands = parse(smt).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    let instances = exec
        .statistics()
        .get_int("ematching_instances_created")
        .unwrap_or(0);
    (outputs.last().cloned().unwrap_or_default(), instances)
}

/// The option a program verifier sends with its patterned axioms.
const TRIGGERS_ONLY: &str = "(set-option :smt.mbqi false)";

/// A binary definition over an uninterpreted sort whose function the ground
/// problem never applies, in an input that asked for triggers only. The pass
/// used to instantiate it at `(a, a)` and `(b, b)`, minting `(f a a)`,
/// `(f b b)` and the `k` terms of the body, which the axiom on `k` then
/// matched: instances of two axioms the contradiction between the last two
/// assertions has nothing to do with (z3: unsat, no instance).
const UNREACHED_DEFINITION: &str = r#"
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
fn an_unreached_definition_over_an_uninterpreted_sort_is_not_instantiated() {
    let (out, instances) = answer_and_instances(UNREACHED_DEFINITION);
    assert_eq!(out, "unsat", "the two ground comparisons contradict");
    assert_eq!(
        instances, 0,
        "no ground term matches a pattern, and the pass mints none"
    );
}

/// The twin differs in one line: the goal applies `f`, so the definition is
/// reached, its instances appear, and the query is satisfiable (`U` the
/// integers, `h` and `k` the identity, `f` addition, `a = -2`, `b = -1`).
#[test]
fn the_twin_that_applies_the_function_is_instantiated_and_not_refuted() {
    let twin =
        UNREACHED_DEFINITION.replace("(assert (< (h b) (h a)))", "(assert (< (h (f a b)) (h a)))");
    assert_ne!(twin, UNREACHED_DEFINITION);
    let (out, instances) = answer_and_instances(&twin);
    assert_ne!(out, "unsat", "the twin has a model");
    assert!(instances > 0, "`(f a b)` matches the definition's pattern");
}

/// The other twin differs in one line too: without the option the input
/// leaves the solver free to look past its patterns, and the pass
/// instantiates the definition at the two constants as it always did. The
/// answer is the same; the instances are what the option keeps away.
#[test]
fn without_the_option_the_unreached_definition_keeps_its_diagonal_instances() {
    let twin = UNREACHED_DEFINITION.replace(TRIGGERS_ONLY, "");
    assert_ne!(twin, UNREACHED_DEFINITION);
    let (out, instances) = answer_and_instances(&twin);
    assert_eq!(out, "unsat", "the two ground comparisons contradict");
    assert!(
        instances > 0,
        "`(f a a)` and `(f b b)` were minted and matched"
    );
}

/// A formula that only the diagonal instance of an unreached definition
/// refutes: at `x = y = d` the body says `h (f d d) = 2 * (h d)` and
/// `h d > h (f d d)`, so `h d < 0`, against the ground fact. Nothing applies
/// `f`, so the pattern has no match (z3: unsat).
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
fn an_unreached_definition_is_refuted_at_the_diagonal() {
    let out = check_sat_output(REFUTED_AT_THE_DIAGONAL);
    assert_eq!(
        out, "unsat",
        "the instance at `(d, d)` contradicts `h d > 0`"
    );
}

/// The twin differs in one line: the ground fact is `h d < 0`, which is what
/// the definition forces. It has a model (`U` the negative integers, `h` the
/// identity, `f` addition), so it must not be refuted.
#[test]
fn the_twin_the_diagonal_agrees_with_is_not_refuted() {
    let twin = REFUTED_AT_THE_DIAGONAL.replace("(assert (> (h d) 0))", "(assert (< (h d) 0))");
    assert_ne!(twin, REFUTED_AT_THE_DIAGONAL);
    let out = check_sat_output(&twin);
    assert_ne!(out, "unsat", "the twin has a model");
}

/// The same formula from an input that asked for triggers only: the
/// definition is not instantiated, as with the reference solver under that
/// option, which then answers `unknown`. The formula is unsatisfiable, so the
/// answer is never `sat`.
#[test]
fn a_triggers_only_input_gets_no_diagonal_instance_of_the_unreached_definition() {
    let input = format!("{TRIGGERS_ONLY}{REFUTED_AT_THE_DIAGONAL}");
    let (out, instances) = answer_and_instances(&input);
    assert_ne!(out, "sat", "the formula has no model");
    assert_eq!(instances, 0, "nothing applies `f`, and the pass mints none");
}

/// The same definition as the hypothesis of a goal, from an input that asked
/// for triggers only: `(not (=> hypothesis (<= (h d) 0)))`. The universal is
/// part of a larger assertion, so the pass keeps it, and its instance at
/// `(d, d)` gives `h d < 0`, which is the goal (z3 with the option: unsat).
/// Asserted by itself, the same universal gets no instance: the test above.
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
fn a_triggers_only_input_keeps_the_diagonal_instance_of_a_hypothesis() {
    let (out, instances) = answer_and_instances(HYPOTHESIS_REFUTED_AT_THE_DIAGONAL);
    assert_eq!(out, "unsat", "the instance at `(d, d)` gives the goal");
    assert!(instances > 0, "the hypothesis was instantiated");
}

/// The twin differs in one line: the goal is `h d >= 0`, which the
/// hypothesis contradicts. Its negation has a model (`U` the negative
/// integers, `h` the identity, `f` addition), so it must not be refuted.
#[test]
fn the_twin_whose_goal_the_hypothesis_contradicts_is_not_refuted() {
    let twin = HYPOTHESIS_REFUTED_AT_THE_DIAGONAL.replace("(<= (h d) 0))))", "(>= (h d) 0))))");
    assert_ne!(twin, HYPOTHESIS_REFUTED_AT_THE_DIAGONAL);
    let out = check_sat_output(&twin);
    assert_ne!(out, "unsat", "the twin has a model");
}

/// A definition the ground problem does reach: `(f d e)` matches the pattern.
/// The refutation still needs the self-pair, which no ground term supplies:
/// at `x = y = d` the premise `(f d d) = (f d d)` holds, so `q d`, against the
/// last assertion. Matching gives the instances at `(d, e)` and `(e, d)`
/// only, and both are satisfied with `(f d e)` different from `(f e d)`
/// (z3: unsat).
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
fn a_reached_definition_is_refuted_at_the_diagonal() {
    let out = check_sat_output(REACHED_AND_REFUTED_AT_THE_DIAGONAL);
    assert_eq!(out, "unsat", "the instance at `(d, d)` gives `q d`");
}

/// The twin differs in one line: the ground fact is `q d`. It has a model
/// (`q` true everywhere), so it must not be refuted.
#[test]
fn the_twin_that_asserts_what_the_diagonal_gives_is_not_refuted() {
    let twin =
        REACHED_AND_REFUTED_AT_THE_DIAGONAL.replace("(assert (not (q d)))", "(assert (q d))");
    assert_ne!(twin, REACHED_AND_REFUTED_AT_THE_DIAGONAL);
    let out = check_sat_output(&twin);
    assert_ne!(out, "unsat", "the twin has a model");
}

/// The same formula from an input that asked for triggers only. The pattern
/// matches `(f d e)` and the `(f e d)` its instance mints, and those two
/// instances are all the definition gets, as with the reference solver under
/// that option (which then answers `unknown`). Without the option the pass
/// adds the instances at `(d, d)` and `(e, e)` on top.
#[test]
fn a_triggers_only_input_gets_the_matched_instances_of_a_reached_definition_only() {
    let (unrestricted, with_diagonal) = answer_and_instances(REACHED_AND_REFUTED_AT_THE_DIAGONAL);
    assert_eq!(unrestricted, "unsat");
    let input = format!("{TRIGGERS_ONLY}{REACHED_AND_REFUTED_AT_THE_DIAGONAL}");
    let (out, matched) = answer_and_instances(&input);
    assert_ne!(out, "sat", "the formula has no model");
    assert!(matched > 0, "`(f d e)` matches the pattern");
    assert!(
        matched < with_diagonal,
        "{matched} instances under triggers only, {with_diagonal} without the option"
    );
}

/// The self-pair refutation the pass exists for: the refutation needs the
/// instance at `X0 = X1 = d`, and only `(s d b)` is present to match
/// (z3: unsat).
#[test]
fn self_pair_over_an_uninterpreted_sort_is_refuted() {
    let out = check_sat_output(
        r#"
        (set-logic UF)
        (declare-sort U 0)
        (declare-fun p (U) Bool)
        (declare-fun s (U U) Bool)
        (declare-const b U)
        (declare-const d U)
        (assert (not (p d)))
        (assert (forall ((X0 U) (X1 U)) (= (=> (p X0) (s X0 X1)) (p X1))))
        (assert (s d b))
        (check-sat)
    "#,
    );
    assert_eq!(out, "unsat", "the self-pair instance refutes this formula");
}

/// A pattern does not take a universal out of the pass: the same formula with
/// a pattern the self-pair never matches is still refuted (z3: unsat).
#[test]
fn self_pair_with_a_pattern_is_refuted() {
    let out = check_sat_output(
        r#"
        (set-logic UF)
        (declare-sort U 0)
        (declare-fun p (U) Bool)
        (declare-fun s (U U) Bool)
        (declare-const b U)
        (declare-const d U)
        (assert (not (p d)))
        (assert (forall ((X0 U) (X1 U))
            (! (= (=> (p X0) (s X0 X1)) (p X1)) :pattern ((s X0 X1)))))
        (assert (s d b))
        (check-sat)
    "#,
    );
    assert_eq!(out, "unsat", "the self-pair instance refutes this formula");
}

/// The same formula over `Int`. Its body applies no function to the binders,
/// so the pass still takes it and supplies the self-pair (z3: unsat).
#[test]
fn function_free_self_pair_over_int_is_refuted() {
    let out = check_sat_output(
        r#"
        (declare-fun p (Int) Bool)
        (declare-fun s (Int Int) Bool)
        (declare-const b Int)
        (declare-const d Int)
        (assert (not (p d)))
        (assert (forall ((X0 Int) (X1 Int))
            (! (= (=> (p X0) (s X0 X1)) (p X1)) :pattern ((s X0 X1)))))
        (assert (s d b))
        (check-sat)
    "#,
    );
    assert_eq!(out, "unsat", "the self-pair instance refutes this formula");
}

/// Verus's prelude defines multiplication by a same-sort universal over `Int`
/// whose body applies `*` to the binders, so the pass leaves it alone. A
/// diagonal instance of it would assert the ground product `(* 3 3)` next to a
/// datatype and a Real-valued function, a theory mix with no combined decision
/// procedure. The pattern `(Mul x y)` has no ground match, so the axiom is
/// irrelevant to the goal, which the datatype theory refutes (z3: unsat).
#[test]
fn int_arithmetic_definition_does_not_block_the_goal() {
    let out = check_sat_output(
        r#"
        (declare-sort Poly 0)
        (declare-fun %R (Poly) Real)
        (declare-fun Mul (Int Int) Int)
        (assert (forall ((x Int) (y Int)) (! (= (Mul x y) (* x y)) :pattern ((Mul x y)))))
        (declare-datatypes ((D 0)) (((This (This/0 Int)) (That (That/v Int)))))
        (declare-const t D)
        (assert (= t (That 3)))
        (assert (not (= (That/v t) 3)))
        (check-sat)
    "#,
    );
    assert_eq!(
        out, "unsat",
        "the datatype goal is refuted without the Mul axiom"
    );
}
