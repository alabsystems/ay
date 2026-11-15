// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The restoring pass installs a spelling on the strength of the printer's
//! confinement only when the printer, run over the finished map, confines it.

use super::*;
use ay_core::kani_compat::DetHashMap;
use ay_core::Sort;
use ay_frontend::command::Command;
use num_bigint::BigInt;

fn parsed_assertion(source: &str) -> FrontendTerm {
    let commands = ay_frontend::parse(source).expect("assertion fixture parses");
    let [Command::Assert(term)] = commands.as_slice() else {
        panic!("fixture must contain one assertion")
    };
    term.clone()
}

/// `assume root`, `assume (not root)`, `(cl)`.
fn refutation(root: TermId, negated: TermId) -> Proof {
    let mut proof = Proof::new();
    let positive = proof.add_assume(root, None);
    let negative = proof.add_assume(negated, None);
    proof.add_resolution(Vec::new(), root, positive, negative);
    proof
}

fn seed(executor: &mut Executor, entries: &[(TermId, &str)]) {
    let overrides: DetHashMap<TermId, String> = entries
        .iter()
        .map(|(term, text)| (*term, (*text).to_string()))
        .collect();
    executor.last_proof_term_overrides = (!overrides.is_empty()).then_some(overrides);
}

fn entry(executor: &Executor, term: TermId) -> Option<String> {
    executor
        .last_proof_term_overrides
        .as_ref()
        .and_then(|overrides| overrides.get(&term).cloned())
}

/// An authored `(=> (= i j) false)` over the canonical `(not (= i j))` is a
/// FOLD the printer derives with `implies_simplify`, so this pass restores it
/// (it was the unconfinable example until the Boolean-fold leaf existed).
#[test]
fn a_folded_implication_root_restores_its_authored_spelling() {
    let mut executor = Executor::new();
    let i = executor.ctx.terms.mk_var("i", Sort::Int);
    let j = executor.ctx.terms.mk_var("j", Sort::Int);
    let equality = executor
        .ctx
        .terms
        .mk_app(Symbol::named("="), [i, j], Sort::Bool);
    let disequality = executor.ctx.terms.mk_not_raw(equality);
    executor
        .ctx
        .add_assertion_with_parsed(equality, parsed_assertion("(assert (= i j))"));
    executor
        .ctx
        .add_assertion_with_parsed(disequality, parsed_assertion("(assert (=> (= i j) false))"));

    let proof = refutation(equality, disequality);
    executor.last_proof_term_overrides = None;
    executor.restore_reachable_authored_assume_surface_overrides(&proof);

    assert!(!executor.last_unsat_proof_reconstruction_suppressed);
    let overrides = executor
        .last_proof_term_overrides
        .clone()
        .expect("the folded implication root records its authored text");
    assert_eq!(
        overrides.get(&disequality).map(String::as_str),
        Some("(=> (= i j) false)")
    );
    let document = ay_proof::try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &executor.ctx.terms,
        &[equality, disequality],
        Some(&overrides),
    )
    .expect("the restored implication has a checked fold bridge");
    assert!(
        document.contains("(assume t1.a (=> (= i j) false))")
            && document.contains(":rule implies_simplify"),
        "{document}"
    );
}

/// `(< (+ x 1) 3)` authored `(or (< (+ x 1) 3) false)`, beside the refuting
/// `(not (< (+ x 1) 3))`.
fn folded_row_fixture(executor: &mut Executor) -> (TermId, TermId, TermId) {
    let x = executor.ctx.terms.mk_var("x", Sort::Int);
    let one = executor.ctx.terms.mk_int(BigInt::from(1));
    let three = executor.ctx.terms.mk_int(BigInt::from(3));
    let sum = executor
        .ctx
        .terms
        .mk_app(Symbol::named("+"), [x, one], Sort::Int);
    let root = executor
        .ctx
        .terms
        .mk_app(Symbol::named("<"), [sum, three], Sort::Bool);
    let negated = executor.ctx.terms.mk_not_raw(root);
    executor
        .ctx
        .add_assertion_with_parsed(root, parsed_assertion("(assert (or (< (+ x 1) 3) false))"));
    executor
        .ctx
        .add_assertion_with_parsed(negated, parsed_assertion("(assert (not (< (+ x 1) 3)))"));
    (root, negated, sum)
}

/// The per-root admission cannot see the rest of the document: here it
/// admits the folded row, but an earlier pass left `(+ 1 x)` document-wide on
/// the descendant `(+ x 1)`, so the printer, run over the finished map,
/// declines the fold and would have left `(or (< (+ x 1) 3) false)` on every
/// occurrence of the root. The spelling is withdrawn to what the root carried
/// before (nothing), exactly the pass's behaviour before folded rows were
/// restored, and nothing is suppressed.
#[test]
fn a_folded_spelling_the_document_does_not_confine_is_withdrawn() {
    let mut executor = Executor::new();
    let (root, negated, sum) = folded_row_fixture(&mut executor);
    let proof = refutation(root, negated);
    assert!(executor.printer_confines_authored_spelling(root, "(or (< (+ x 1) 3) false)"));

    seed(&mut executor, &[(sum, "(+ 1 x)")]);
    executor.restore_reachable_authored_assume_surface_overrides(&proof);
    assert!(!executor.last_unsat_proof_reconstruction_suppressed);
    assert_eq!(entry(&executor, root), None, "withdrawn, not installed");
    assert_eq!(entry(&executor, sum).as_deref(), Some("(+ 1 x)"));

    // Twin: with nothing re-spelled the same row is restored.
    let mut executor = Executor::new();
    let (root, negated, _) = folded_row_fixture(&mut executor);
    executor.restore_reachable_authored_assume_surface_overrides(&refutation(root, negated));
    assert!(!executor.last_unsat_proof_reconstruction_suppressed);
    assert_eq!(
        entry(&executor, root).as_deref(),
        Some("(or (< (+ x 1) 3) false)")
    );
}

/// `p` authored `(or p false)`, beside the refuting `(not p)`, and the term
/// `(and p q)`.
fn variable_row_fixture(executor: &mut Executor, authored: &str) -> (TermId, TermId, TermId) {
    let p = executor.ctx.terms.mk_var("p", Sort::Bool);
    let q = executor.ctx.terms.mk_var("q", Sort::Bool);
    let conjunction = executor
        .ctx
        .terms
        .mk_app(Symbol::named("and"), [p, q], Sort::Bool);
    let negated = executor.ctx.terms.mk_not_raw(p);
    executor
        .ctx
        .add_assertion_with_parsed(p, parsed_assertion(authored));
    executor
        .ctx
        .add_assertion_with_parsed(negated, parsed_assertion("(assert (not p))"));
    (p, negated, conjunction)
}

/// A whole-assertion spelling on a VARIABLE root is installed only because
/// the printer confines it; when the printer, over the finished map,
/// declines it (an earlier pass left `(and q p)` document-wide on the
/// ancestor `(and p q)`), the whole map declines, exactly as the atom-hijack
/// guard did before such spellings existed.
#[test]
fn a_guarded_spelling_the_document_does_not_confine_declines_the_map() {
    let mut executor = Executor::new();
    let (p, negated, conjunction) = variable_row_fixture(&mut executor, "(assert (or p false))");
    seed(&mut executor, &[(conjunction, "(and q p)")]);
    executor.restore_reachable_authored_assume_surface_overrides(&refutation(p, negated));
    assert!(executor.last_unsat_proof_reconstruction_suppressed);

    // Twin: with nothing re-spelled the variable root carries its row.
    let mut executor = Executor::new();
    let (p, negated, _) = variable_row_fixture(&mut executor, "(assert (or p false))");
    executor.restore_reachable_authored_assume_surface_overrides(&refutation(p, negated));
    assert!(!executor.last_unsat_proof_reconstruction_suppressed);
    assert_eq!(entry(&executor, p).as_deref(), Some("(or p false)"));
}

/// NEGATIVE TWIN of the variable-root arm: a whole-assertion spelling no
/// checked step folds onto the variable (`(< 1 0)` is not the literal `false`
/// `or_simplify` drops) is refused by the atom-hijack guard and declines the
/// map; it is never installed.
#[test]
fn an_unconfinable_variable_spelling_still_declines_the_map() {
    let mut executor = Executor::new();
    let (p, negated, _) = variable_row_fixture(&mut executor, "(assert (or p (< 1 0)))");
    executor.restore_reachable_authored_assume_surface_overrides(&refutation(p, negated));
    assert!(executor.last_unsat_proof_reconstruction_suppressed);
    assert_eq!(entry(&executor, p), None);
}

/// `(<= 0 (f b))` authored as `authored`, beside the refuting negation.
fn comparison_row_fixture(executor: &mut Executor, authored: &str) -> (TermId, TermId) {
    let b = executor.ctx.terms.mk_var("b", Sort::Int);
    let f_b = executor
        .ctx
        .terms
        .mk_app(Symbol::named("f"), [b], Sort::Int);
    let zero = executor.ctx.terms.mk_int(BigInt::from(0));
    let root = executor
        .ctx
        .terms
        .mk_app(Symbol::named("<="), [zero, f_b], Sort::Bool);
    let negated = executor.ctx.terms.mk_not_raw(root);
    executor
        .ctx
        .add_assertion_with_parsed(root, parsed_assertion(authored));
    executor
        .ctx
        .add_assertion_with_parsed(negated, parsed_assertion("(assert (not (<= 0 (f b))))"));
    (root, negated)
}

/// A row whose spelling disagrees with the entry an earlier pass left on its
/// root overwrites that entry only when the printer confines the row's
/// spelling to its `assume`: `(>= (f b) 0)` (`comp_simplify`) replaces the
/// stale entry, while NEGATIVE TWIN `(<= (- 1 1) (f b))` (no checked step
/// turns `(- 1 1)` into `0`) still declines the whole map.
#[test]
fn a_conflicting_row_spelling_replaces_the_entry_only_when_confined() {
    let mut executor = Executor::new();
    let (root, negated) = comparison_row_fixture(&mut executor, "(assert (>= (f b) 0))");
    seed(&mut executor, &[(root, "(<= 0 (+ (f b) 0))")]);
    executor.restore_reachable_authored_assume_surface_overrides(&refutation(root, negated));
    assert!(!executor.last_unsat_proof_reconstruction_suppressed);
    assert_eq!(entry(&executor, root).as_deref(), Some("(>= (f b) 0)"));

    let mut executor = Executor::new();
    let (root, negated) = comparison_row_fixture(&mut executor, "(assert (<= (- 1 1) (f b)))");
    seed(&mut executor, &[(root, "(<= 0 (+ (f b) 0))")]);
    executor.restore_reachable_authored_assume_surface_overrides(&refutation(root, negated));
    assert!(
        executor.last_unsat_proof_reconstruction_suppressed,
        "an unconfined conflicting spelling declines the map, as before"
    );
}
