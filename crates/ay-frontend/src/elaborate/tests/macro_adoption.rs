// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Definitional-`forall` macro adoption at binder arities above one.
//!
//! 92e37dcf3 bounded adoption to a single binder and pinned that bound with a
//! test asserting the refusal. The bound was not a soundness property — arity
//! appears nowhere in the definitional-extension argument, and every other
//! guard in `try_adopt_definitional_forall` is written over k binders — while
//! the cost was real: a refused multi-binder definition stays quantified and
//! the AUFLIA lazy split loop does not converge on that family, turning a 2s
//! `sat` into a divergence.
//!
//! So the arity assertion is gone and what replaces it is the property the old
//! test was actually protecting: an assertion may be discharged to the
//! reflexive tautology ONLY in exchange for a registered macro that carries its
//! meaning. Adoption and retention are the two halves of that trade, and both
//! are pinned below.

use super::*;
use crate::command::Command;

fn elaborate(script: &str) -> Context {
    let commands = parse(script).expect("parse");
    let mut context = Context::new();
    for command in &commands {
        context
            .process_command(command)
            .expect("elaboration succeeds");
    }
    context
}

/// A two-binder definitional extension is adopted, and the macro it registers
/// carries BOTH binders — the meaning the discharged assertion gave up.
#[test]
fn multi_binder_definitional_forall_is_adopted_with_all_its_binders() {
    let context = elaborate(
        "(declare-fun f (Int Int) Int) \
         (assert (forall ((x Int) (y Int)) (= (f x y) (+ x y))))",
    );

    let (binders, _) = context
        .adopted_macro_interp("f")
        .expect("a two-binder definitional extension must be adopted");
    assert_eq!(
        binders.len(),
        2,
        "the registered macro must carry every binder of the definition it replaces"
    );
}

/// The discharge is only sound in exchange for the macro, so it is pinned
/// against that exchange rather than on its own: the source constraint becomes
/// the reflexive tautology BECAUSE `f` now expands to its definition.
#[test]
fn adopted_multi_binder_definition_is_discharged_by_its_macro() {
    let context = elaborate(
        "(declare-fun f (Int Int) Int) \
         (assert (forall ((x Int) (y Int)) (= (f x y) (+ x y))))",
    );

    assert!(
        context.adopted_macro_interp("f").is_some(),
        "discharge without a registered macro would drop the constraint"
    );
    assert_eq!(context.assertions.len(), 1);
    let TermData::Forall(_, body, _) = context.terms.get(context.assertions[0]) else {
        // Elaboration may fold the whole tautology away; either form is the
        // same discharged constraint.
        assert_eq!(context.assertions[0], context.terms.true_term());
        return;
    };
    assert_eq!(
        *body,
        context.terms.true_term(),
        "an adopted definition expands to `t = t` and discharges"
    );
}

/// THE SOUNDNESS HALF, and the reason the old test earned its place: when a
/// guard refuses adoption, the source constraint must SURVIVE. Here `f` is
/// already mentioned by an earlier assertion, so adopting would leave that raw
/// occurrence constraining a disconnected symbol while later ones expand.
/// Refusal is required — and refusal must not also discard the definition.
#[test]
fn refused_multi_binder_adoption_retains_the_source_constraint() {
    let context = elaborate(
        "(declare-fun f (Int Int) Int) \
         (assert (> (f 1 2) 0)) \
         (assert (forall ((x Int) (y Int)) (= (f x y) (+ x y))))",
    );

    assert!(
        context.adopted_macro_interp("f").is_none(),
        "a pre-adoption raw occurrence of `f` must refuse adoption"
    );
    assert_eq!(context.assertions.len(), 2);
    let TermData::Forall(vars, body, _) = context.terms.get(context.assertions[1]) else {
        panic!("the refused definition must remain quantified");
    };
    assert_eq!(vars.len(), 2);
    assert_ne!(
        *body,
        context.terms.true_term(),
        "refused adoption must retain the source constraint"
    );
}

// ---------------------------------------------------------------------------
// #defmacro-named-preuse: `:named` definitions and definitions asserted after
// a use of their head (the shape deductive-checks emits for every spec function).
// ---------------------------------------------------------------------------

/// A `:named` wrapper carries no meaning (SMT-LIB 2.6 §3.6.5), so it must not
/// refuse adoption — and the label must still resolve, on the discharged
/// assertion, for `get-unsat-core`.
#[test]
fn named_definitional_forall_is_adopted_at_assert_time() {
    let context = elaborate(
        "(declare-fun f (Int) Bool) \
         (assert (! (forall ((x Int)) (= (f x) (<= 5 x))) :named def)) \
         (assert (! (not (f 7)) :named use))",
    );
    assert!(
        context.adopted_macro_interp("f").is_some(),
        "a :named definitional forall must be adopted"
    );
    assert_eq!(context.assertions.len(), 2);
    assert_eq!(
        context.named_terms.get("def").copied(),
        Some(context.assertions[0]),
        "the label must resolve to the discharged assertion"
    );
    assert!(
        !context.term_mentions_symbol(context.assertions[1], "f"),
        "the later use must expand through the macro"
    );
    assert_eq!(
        context.adopted_definition_labels().collect::<Vec<_>>(),
        vec!["def"],
        "the definition's label is recorded for core reporting"
    );
}

/// A user trigger asks for E-matching semantics: a `:pattern` inside the
/// binder keeps the forall quantified, byte-identically to before.
#[test]
fn pattern_annotated_definitional_forall_is_not_adopted() {
    let context = elaborate(
        "(declare-fun f (Int) Bool) \
         (assert (forall ((x Int)) (! (= (f x) (<= 5 x)) :pattern ((f x))))) \
         (check-sat)",
    );
    assert!(context.adopted_macro_interp("f").is_none());
    assert!(
        matches!(
            context.terms.get(context.assertions[0]),
            TermData::Forall(_, body, _) if *body != context.terms.true_term()
        ),
        "a triggered definition must stay quantified"
    );
}

/// THE PRE-USE CASE (captured deductive-checks `proof_in_spec` query, z3: sat): the
/// use `out = f(i)` is asserted BEFORE the `:named` definition. Assert-time
/// adoption must still refuse (the earlier raw occurrence would be
/// disconnected), and the first `check-sat` must adopt AND re-elaborate the
/// earlier use so no raw `f` survives anywhere on the stack.
#[test]
fn check_sat_adopts_a_definition_asserted_after_a_use_and_expands_that_use() {
    let commands = parse(
        "(declare-fun f (Int) Int) (declare-const i Int) (declare-const out Int) \
         (assert (! (= out (f i)) :named use)) \
         (assert (! (forall ((x Int)) (= (f x) (+ x 1))) :named def)) \
         (assert (! (not (= (f i) 5)) :named goal))",
    )
    .expect("parse");
    let mut context = Context::new();
    for command in &commands {
        context.process_command(command).expect("elaborates");
    }
    assert!(
        context.adopted_macro_interp("f").is_none(),
        "assert-time adoption must refuse a definition whose head is already in use"
    );
    let before = context.assertions.clone();
    assert!(context.term_mentions_symbol(before[0], "f"));

    context
        .process_command(&Command::CheckSat)
        .expect("check-sat elaborates");

    let (binders, _) = context
        .adopted_macro_interp("f")
        .expect("the first check-sat adopts the pre-used definition");
    assert_eq!(binders.len(), 1);
    assert_eq!(context.assertions.len(), 3);
    assert_eq!(context.assertions_parsed.len(), 3);
    for (index, &assertion) in context.assertions.iter().enumerate() {
        assert!(
            !context.term_mentions_symbol(assertion, "f"),
            "assertion {index} must not keep a raw occurrence of the adopted head"
        );
    }
    assert_ne!(
        context.assertions[0], before[0],
        "the earlier use must have been re-elaborated through the macro"
    );
    assert_eq!(
        context.named_terms.get("use").copied(),
        Some(context.assertions[0]),
        "labels follow the re-elaborated assertions"
    );
    assert_eq!(
        context.named_terms.get("def").copied(),
        Some(context.assertions[1])
    );
    assert_eq!(
        context.concrete_authored_assertion_terms(),
        context.assertions,
        "the authored-assertion terms move with the stack"
    );
    assert_eq!(
        context.adopted_definition_labels().collect::<Vec<_>>(),
        vec!["def"]
    );
}

/// A soft assertion retains no parsed AST, so a head it mentions cannot be
/// re-elaborated: the pass must refuse that head and leave the stack alone.
#[test]
fn check_sat_adoption_refuses_a_head_mentioned_by_a_soft_constraint() {
    let commands = parse(
        "(declare-fun f (Int) Int) (declare-const out Int) \
         (assert (= out (f 3))) \
         (assert-soft (> (f 1) 0)) \
         (assert (forall ((x Int)) (= (f x) (+ x 1))))",
    )
    .expect("parse");
    let mut context = Context::new();
    for command in &commands {
        context.process_command(command).expect("elaborates");
    }
    let before = context.assertions.clone();
    context
        .process_command(&Command::CheckSat)
        .expect("check-sat elaborates");
    assert!(context.adopted_macro_interp("f").is_none());
    assert_eq!(
        context.assertions, before,
        "a refusal keeps the stack byte-identical"
    );
}

/// Adoption is an outermost-scope affair: a `pop` could drop the justifying
/// assertion while the macro lived on.
#[test]
fn check_sat_adoption_refuses_inside_a_scope() {
    let commands = parse(
        "(declare-fun f (Int) Int) (declare-const out Int) \
         (assert (= out (f 3))) \
         (push 1) \
         (assert (forall ((x Int)) (= (f x) (+ x 1))))",
    )
    .expect("parse");
    let mut context = Context::new();
    for command in &commands {
        context.process_command(command).expect("elaborates");
    }
    let before = context.assertions.clone();
    context
        .process_command(&Command::CheckSat)
        .expect("check-sat elaborates");
    assert!(context.adopted_macro_interp("f").is_none());
    assert_eq!(context.assertions, before);
}

/// The transaction boundary: when re-elaboration fails after the macros were
/// registered, every macro of the pass is rolled back, the stack and the
/// named-term map are untouched, and the definition is still asserted.
#[test]
fn check_sat_adoption_rolls_back_when_reelaboration_fails() {
    let commands = parse(
        "(declare-fun f (Int) Int) (declare-const out Int) \
         (assert (! (= out (f 3)) :named use)) \
         (assert (! (forall ((x Int)) (= (f x) (+ x 1))) :named def))",
    )
    .expect("parse");
    let mut context = Context::new();
    for command in &commands {
        context.process_command(command).expect("elaborates");
    }
    let assertions_before = context.assertions.clone();
    let named_before = context.named_terms.clone();
    context.fail_next_check_sat_reelaboration();
    context
        .process_command(&Command::CheckSat)
        .expect("a rolled-back pass is not an error");
    assert!(
        context.adopted_macro_interp("f").is_none(),
        "the macro must not outlive the failed re-elaboration"
    );
    assert!(!context.is_defined_fun("f"));
    assert_eq!(context.assertions, assertions_before);
    assert_eq!(context.named_terms, named_before);
    assert_eq!(context.adopted_definition_labels().count(), 0);
    assert!(
        matches!(
            context.terms.get(context.assertions[1]),
            TermData::Forall(_, body, _) if *body != context.terms.true_term()
        ),
        "the refused definition must remain quantified"
    );
}

/// Sequential adoption validates each later candidate with the earlier macros
/// registered, so a definitional cycle is refused exactly as at assert time.
#[test]
fn check_sat_adoption_refuses_a_definitional_cycle() {
    let commands = parse(
        "(declare-fun f (Int) Int) (declare-fun g (Int) Int) \
         (assert (= (f 3) 1)) \
         (assert (forall ((x Int)) (= (f x) (+ (g x) 1)))) \
         (assert (forall ((x Int)) (= (g x) (+ (f x) 1))))",
    )
    .expect("parse");
    let mut context = Context::new();
    for command in &commands {
        context.process_command(command).expect("elaborates");
    }
    context
        .process_command(&Command::CheckSat)
        .expect("check-sat elaborates");
    assert!(context.adopted_macro_interp("f").is_some());
    assert!(
        context.adopted_macro_interp("g").is_none(),
        "`g := f(x) + 1` elaborates to `g(x) = g(x) + 2` once `f` expands: refused"
    );
}

/// Only the first `check-sat` of a session runs the pass: a later one may sit
/// on persistent incremental state that already encoded the raw assertions.
#[test]
fn check_sat_adoption_runs_only_on_the_first_check_sat() {
    let commands = parse(
        "(declare-fun f (Int) Int) (declare-const out Int) \
         (assert (= out (f 3))) \
         (check-sat) \
         (assert (forall ((x Int)) (= (f x) (+ x 1))))",
    )
    .expect("parse");
    let mut context = Context::new();
    for command in &commands {
        context.process_command(command).expect("elaborates");
    }
    let before = context.assertions.clone();
    context
        .process_command(&Command::CheckSat)
        .expect("check-sat elaborates");
    assert!(context.adopted_macro_interp("f").is_none());
    assert_eq!(context.assertions, before);
}

/// Two candidate definitions of one head: the first is adopted and the
/// second becomes a residual constraint over the expansion (module docs);
/// the raw stack is left as the one fallback.
#[test]
fn a_second_definition_of_a_head_becomes_a_residual_constraint() {
    let commands = parse(
        "(declare-fun g (Int) Int) (declare-const i Int) (declare-const out Int) \
         (assert (! (= out (g i)) :named use)) \
         (assert (! (forall ((x Int)) (= (g x) (+ x 1))) :named d1)) \
         (assert (! (forall ((x Int)) (= (g x) 2)) :named d2))",
    )
    .expect("parse");
    let mut context = Context::new();
    for command in &commands {
        context.process_command(command).expect("elaborates");
    }
    let raw_assertions = context.assertions.clone();
    context
        .process_command(&Command::CheckSat)
        .expect("check-sat elaborates");
    assert!(context.adopted_macro_interp("g").is_some());
    assert_eq!(
        context.adopted_definition_labels().collect::<Vec<_>>(),
        vec!["d1"],
        "the first definition is the macro"
    );
    for (index, &assertion) in context.assertions.iter().enumerate() {
        assert!(
            !context.term_mentions_symbol(assertion, "g"),
            "assertion {index} must be expanded (the second definition is a residual)"
        );
    }
    let mut chain = context.take_definitional_adoption_retry();
    assert_eq!(chain.len(), 1, "the raw stack is the one fallback");
    context.restore_definitional_adoption_snapshot(chain.remove(0));
    assert!(context.adopted_macro_interp("g").is_none());
    assert_eq!(context.assertions, raw_assertions);
}

/// The assert-time finder adopted the first definition it saw; the pass
/// re-adopts it for the live stack (the second definition is a residual)
/// and leaves BOTH the raw stack and the assert-time stack to fall back to.
#[test]
fn the_fallback_chain_holds_the_raw_and_the_assert_time_stacks() {
    let commands = parse(
        "(declare-fun g (Int) Int) (declare-const i Int) (declare-const out Int) \
         (assert (! (forall ((x Int)) (= (g x) (+ x 1))) :named d1)) \
         (assert (! (forall ((x Int)) (= (g x) 2)) :named d2)) \
         (assert (! (= out (g i)) :named use))",
    )
    .expect("parse");
    let mut context = Context::new();
    for command in &commands {
        context.process_command(command).expect("elaborates");
    }
    assert!(
        context.adopted_macro_interp("g").is_some(),
        "the assert-time finder adopts the first definition"
    );
    let assert_time_assertions = context.assertions.clone();
    assert!(!context.term_mentions_symbol(assert_time_assertions[2], "g"));

    context
        .process_command(&Command::CheckSat)
        .expect("check-sat elaborates");
    assert!(
        context.adopted_macro_interp("g").is_some(),
        "re-adopted for the live stack"
    );
    assert_eq!(
        context.adopted_definition_labels().collect::<Vec<_>>(),
        vec!["d1"]
    );
    assert!(!context.term_mentions_symbol(context.assertions[2], "g"));

    let mut chain = context.take_definitional_adoption_retry();
    assert_eq!(chain.len(), 2, "raw first, then the assert-time stack");
    context.restore_definitional_adoption_snapshot(chain.remove(0));
    assert!(
        context.adopted_macro_interp("g").is_none(),
        "the raw stack has no macro"
    );
    assert_eq!(context.adopted_definition_labels().count(), 0);
    for (index, &assertion) in context.assertions.iter().enumerate() {
        assert!(
            context.term_mentions_symbol(assertion, "g"),
            "assertion {index} must be raw"
        );
    }
    assert_eq!(
        context.named_terms.get("use").copied(),
        Some(context.assertions[2]),
        "labels follow the re-elaborated assertions"
    );
    assert_eq!(
        context.concrete_authored_assertion_terms(),
        context.assertions
    );

    context.restore_definitional_adoption_snapshot(chain.remove(0));
    assert!(
        context.adopted_macro_interp("g").is_some(),
        "the assert-time adoption is reinstated"
    );
    assert_eq!(
        context.adopted_definition_labels().collect::<Vec<_>>(),
        vec!["d1"],
        "with its label"
    );
    assert_eq!(context.assertions, assert_time_assertions);
    assert!(context.take_definitional_adoption_retry().is_empty());
}

/// After an adoption the pass leaves the raw stack behind for the executor;
/// restoring it puts back every moved piece — stack, labels, authored
/// records, macros — and the snapshot is taken exactly once.
#[test]
fn check_sat_adoption_leaves_a_retry_snapshot_that_restores_the_raw_stack() {
    let commands = parse(
        "(declare-fun f (Int) Int) (declare-const i Int) (declare-const out Int) \
         (assert (! (= out (f i)) :named use)) \
         (assert (! (forall ((x Int)) (= (f x) (+ x 1))) :named def))",
    )
    .expect("parse");
    let mut context = Context::new();
    for command in &commands {
        context.process_command(command).expect("elaborates");
    }
    let raw_assertions = context.assertions.clone();
    let raw_named = context.named_terms.clone();
    let raw_authored = context.concrete_authored_assertion_terms();
    let raw_metadata = context.assertion_finite_set_metadata.clone();

    context
        .process_command(&Command::CheckSat)
        .expect("check-sat elaborates");
    assert!(context.adopted_macro_interp("f").is_some());
    assert_ne!(context.assertions, raw_assertions);
    let mut chain = context.take_definitional_adoption_retry();
    assert_eq!(
        chain.len(),
        1,
        "an adoption leaves the raw stack for the executor"
    );
    assert!(
        context.take_definitional_adoption_retry().is_empty(),
        "the chain is taken exactly once"
    );

    context.restore_definitional_adoption_snapshot(chain.remove(0));
    assert!(context.adopted_macro_interp("f").is_none());
    assert!(!context.is_defined_fun("f"));
    assert_eq!(context.adopted_definition_labels().count(), 0);
    assert_eq!(context.assertions, raw_assertions);
    assert_eq!(context.named_terms, raw_named);
    assert_eq!(context.concrete_authored_assertion_terms(), raw_authored);
    assert_eq!(context.assertion_finite_set_metadata, raw_metadata);
    assert_eq!(
        context.assertions_parsed.len(),
        2,
        "the parsed stack was never touched"
    );
    assert!(context.term_mentions_symbol(context.assertions[0], "f"));
    assert!(context.take_definitional_adoption_retry().is_empty());
}

/// The executor's second solve of the raw stack is the same query: it
/// re-runs `check-sat` elaboration, so the single-shot accounting must be
/// rewound first.
#[test]
fn uncount_check_sat_for_retry_keeps_the_query_single_shot() {
    let mut context = elaborate("(declare-const p Bool) (assert p)");
    context
        .process_command(&Command::CheckSat)
        .expect("check-sat elaborates");
    assert!(context.is_single_shot_query());
    context.uncount_check_sat_for_retry();
    context
        .process_command(&Command::CheckSat)
        .expect("the re-run elaborates");
    assert!(
        context.is_single_shot_query(),
        "the re-run is not a second query"
    );
    context
        .process_command(&Command::CheckSat)
        .expect("a genuine second check-sat elaborates");
    assert!(!context.is_single_shot_query());
}

/// The pass's own budgeted parsed copy (the CLI's posture when no proof
/// can be emitted): proof-surface retention stays OFF — `assertions_parsed`
/// never grows — yet a small stack is fully copied and the pass runs; once
/// the budget is spent the copy stops and the pass, which needs a fully
/// aligned stack, declines. `(reset)` re-arms the budget; `:produce-proofs`
/// retains the full surface, which the pass then reads.
#[test]
fn the_pass_own_parsed_copy_reaches_it_until_the_budget_is_spent() {
    let script = "(declare-fun f (Int) Int) (declare-const i Int) (declare-const out Int) \
         (assert (= out (f i))) \
         (assert (forall ((x Int)) (= (f x) (+ x 1))))";
    let commands = parse(script).expect("parse");

    let mut within = Context::new();
    within.set_retain_parsed_assertions(false);
    within.set_definitional_pass_parsed_budget(1_000);
    for command in &commands {
        within.process_command(command).expect("elaborates");
    }
    assert!(
        within.assertions_parsed.is_empty(),
        "the proof surface is not retained"
    );
    assert_eq!(
        within.definitional_pass.parsed.len(),
        within.assertions.len()
    );
    within
        .process_command(&Command::CheckSat)
        .expect("check-sat elaborates");
    assert!(
        within.adopted_macro_interp("f").is_some(),
        "within the budget the pass runs exactly as under full retention"
    );
    assert!(within.assertions_parsed.is_empty());
    for (index, &assertion) in within.assertions.iter().enumerate() {
        assert!(
            !within.term_mentions_symbol(assertion, "f"),
            "assertion {index} must be expanded"
        );
    }
    assert_eq!(
        within.concrete_authored_assertion_terms(),
        within.assertions,
        "the authored records follow the stack without a parsed index"
    );

    let mut spent = Context::new();
    spent.set_retain_parsed_assertions(false);
    spent.set_definitional_pass_parsed_budget(3);
    for command in &commands {
        spent.process_command(command).expect("elaborates");
    }
    assert!(spent.definitional_pass.parsed.len() < spent.assertions.len());
    let before = spent.assertions.clone();
    spent
        .process_command(&Command::CheckSat)
        .expect("check-sat elaborates");
    assert!(spent.adopted_macro_interp("f").is_none());
    assert_eq!(spent.assertions, before);

    spent
        .process_command(&Command::Reset)
        .expect("reset elaborates");
    for command in &commands {
        spent.process_command(command).expect("elaborates");
    }
    assert!(
        spent.definitional_pass.parsed.len() < spent.assertions.len(),
        "`(reset)` re-arms the same budget, which the same stack spends again"
    );
    let produce_proofs = parse("(set-option :produce-proofs true)").expect("parse");
    for command in &produce_proofs {
        spent.process_command(command).expect("elaborates");
    }
    assert!(
        spent.retains_parsed_assertions(),
        "`:produce-proofs` retains the surface"
    );
}

/// The captured contested shape with all three definitions first (`g` twice,
/// then `f` through `g`): the live stack keeps `g`'s first definition and
/// refuses the now-recursive `f`; the raw stack comes first in the chain
/// and the assert-time stack last.
#[test]
fn a_recursive_sibling_is_refused_and_the_chain_ends_at_the_assert_time_stack() {
    let commands = parse(
        "(declare-const a Int) (declare-const c Int) (declare-const d Int) \
         (declare-fun f (Int) Int) (declare-fun g (Int Int) Int) \
         (assert (! (forall ((x Int) (y Int)) (= (g x y) (f (f x)))) :named n1)) \
         (assert (! (forall ((x Int) (y Int)) (= (g x y) a)) :named n2)) \
         (assert (! (forall ((x Int)) (= (f x) (* 2 (g x d)))) :named n3)) \
         (assert (distinct (f 2) (g 5 2) (+ c c)))",
    )
    .expect("parse");
    let mut context = Context::new();
    for command in &commands {
        context.process_command(command).expect("elaborates");
    }
    assert!(context.adopted_macro_interp("g").is_some());
    assert!(context.adopted_macro_interp("f").is_none());
    context
        .process_command(&Command::CheckSat)
        .expect("check-sat elaborates");
    assert!(
        context.adopted_macro_interp("g").is_some(),
        "the live stack keeps the first definition of g"
    );
    assert!(
        context.adopted_macro_interp("f").is_none(),
        "f's body expands through g into a recursion and is refused"
    );
    let mut chain = context.take_definitional_adoption_retry();
    assert_eq!(
        chain.len(),
        2,
        "first the raw stack, then the assert-time stack"
    );
    context.restore_definitional_adoption_snapshot(chain.remove(0));
    assert!(context.adopted_macro_interp("f").is_none());
    assert!(context.adopted_macro_interp("g").is_none());
    for (index, &assertion) in context.assertions.iter().enumerate() {
        assert!(
            context.term_mentions_symbol(assertion, "g"),
            "assertion {index} must be raw again"
        );
    }
    context.restore_definitional_adoption_snapshot(chain.remove(0));
    assert!(context.adopted_macro_interp("f").is_none());
    assert!(
        context.adopted_macro_interp("g").is_some(),
        "the assert-time adoption of g is reinstated last"
    );
    assert!(
        !context.term_mentions_symbol(context.assertions[3], "g"),
        "the use is expanded through g again"
    );
}

/// The executor's proof reconstruction feeds a retained assertion to a
/// `check-sat-assuming` command on the live context purely to elaborate it,
/// in the middle of a public decision (`collect_hidden_problem_equality_assertions`).
/// Held, that command adopts nothing and leaves the stack, the named-term map
/// and the source revision byte-identical — the elaborated assumption is the
/// raw term already on the stack — and the pass still runs at the next REAL
/// check: the hold does not spend its once-per-session entry.
#[test]
fn a_held_check_sat_command_neither_adopts_nor_spends_the_pass() {
    let commands = parse(
        "(declare-fun f (Int) Int) (declare-const i Int) (declare-const out Int) \
         (assert (= out (f i))) \
         (assert (forall ((x Int)) (= (f x) (+ x 1))))",
    )
    .expect("parse");
    let mut context = Context::new();
    for command in &commands {
        context.process_command(command).expect("elaborates");
    }
    assert!(
        context.adopted_macro_interp("f").is_none(),
        "assert-time adoption refuses the pre-used definition"
    );
    let before = context.assertions.clone();
    let stamp = context.source_context_stamp();
    let assumption = context.assertions_parsed[0].clone();

    let elaborated = context
        .with_definitional_check_sat_pass_held(|context| {
            context.process_command(&Command::CheckSatAssuming(vec![assumption]))
        })
        .expect("the held command still elaborates");
    let Some(CommandResult::CheckSatAssuming(term_ids)) = elaborated else {
        panic!("a check-sat-assuming command answers with its elaborated assumptions");
    };
    assert_eq!(
        term_ids,
        &before[..1],
        "held: the assumption elaborates to the raw term already on the stack"
    );
    assert!(
        context.adopted_macro_interp("f").is_none(),
        "held: nothing is adopted"
    );
    assert_eq!(context.assertions, before, "held: the stack is untouched");
    assert!(
        context.source_context_stamp() == stamp,
        "held: the source revision is untouched"
    );
    assert!(
        context.take_definitional_adoption_retry().is_empty(),
        "held: no fallback chain is left behind"
    );

    context
        .process_command(&Command::CheckSat)
        .expect("check-sat elaborates");
    assert!(
        context.adopted_macro_interp("f").is_some(),
        "the next real check-sat still runs the pass"
    );
    assert_ne!(
        context.assertions[0], before[0],
        "and it re-elaborates the earlier use through the macro"
    );
}
