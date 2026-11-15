// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! An authored equality whose canonical root is its field-wise expansion
//! publishes the AUTHORED equality at its `assume`.
//!
//! Datatype flattening turns `(assert (= a b))` into the canonical root
//! `(and (= a!ptr b!ptr) (= a!len b!len))`. Withheld as unconfinable, that
//! expansion was printed as the `assume` itself, which is no assertion of the
//! problem file (pinned carcara: "could not match term to any of the original
//! problem premises"). The printer derives the expansion from the authored
//! equality with one `cong` per conjunct, so the root is admitted and the
//! authored text is installed.

use super::*;
use ay_frontend::command::Command;

fn parsed_assertion(source: &str) -> FrontendTerm {
    let commands = ay_frontend::parse(source).expect("assertion fixture parses");
    let [Command::Assert(term)] = commands.as_slice() else {
        panic!("fixture must contain one assertion")
    };
    term.clone()
}

/// `(and (= a!ptr b!ptr) second)` authored as `(= a b)`, refuted against the
/// authored `(not (= (ptr a) (ptr b)))`; returns the executor after the final
/// presentation pass and the expansion root.
fn restore_expansion(second: impl FnOnce(&mut TermStore) -> TermId) -> (Executor, TermId) {
    let mut executor = Executor::new();
    let terms = &mut executor.ctx.terms;
    let a_ptr = terms.mk_var("a!ptr", Sort::Int);
    let b_ptr = terms.mk_var("b!ptr", Sort::Int);
    let first = terms.mk_app(Symbol::named("="), [a_ptr, b_ptr], Sort::Bool);
    let second = second(terms);
    let expansion = terms.mk_app(Symbol::named("and"), [first, second], Sort::Bool);
    let refuted = terms.mk_not_raw(first);
    executor
        .ctx
        .add_assertion_with_parsed(expansion, parsed_assertion("(assert (= a b))"));
    executor.ctx.add_assertion_with_parsed(
        refuted,
        parsed_assertion("(assert (not (= (ptr a) (ptr b))))"),
    );
    let mut proof = Proof::new();
    let assumed = proof.add_assume(expansion, None);
    let negative = proof.add_assume(refuted, None);
    proof.add_resolution(Vec::new(), expansion, assumed, negative);
    executor.restore_reachable_authored_assume_surface_overrides(&proof);
    (executor, expansion)
}

fn installed(executor: &Executor, root: TermId) -> Option<&str> {
    executor
        .last_proof_term_overrides
        .as_ref()
        .and_then(|overrides| overrides.get(&root))
        .map(String::as_str)
}

#[test]
fn a_field_wise_equality_expansion_publishes_the_authored_equality() {
    let (executor, expansion) = restore_expansion(|terms| {
        let a_len = terms.mk_var("a!len", Sort::Int);
        let b_len = terms.mk_var("b!len", Sort::Int);
        terms.mk_app(Symbol::named("="), [a_len, b_len], Sort::Bool)
    });
    assert!(
        !executor.last_unsat_proof_reconstruction_suppressed,
        "the expansion has exactly one authored row; admitting it is presentation only"
    );
    assert_eq!(installed(&executor, expansion), Some("(= a b)"));
}

/// A conjunct that is not an equality is not a field-wise expansion: the root
/// stays withheld, exactly as before.
#[test]
fn a_conjunction_with_a_non_equality_conjunct_stays_withheld() {
    let (executor, expansion) = restore_expansion(|terms| terms.mk_var("p", Sort::Bool));
    assert!(!executor.last_unsat_proof_reconstruction_suppressed);
    assert_eq!(installed(&executor, expansion), None);
}
