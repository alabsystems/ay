// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

fn executor(script: &str) -> Executor {
    let mut executor = Executor::new();
    executor.set_produce_proofs(true);
    executor
        .execute_all(&ay_frontend::parse(script).expect("parse"))
        .expect("declare");
    executor
}

fn raw(executor: &mut Executor, surface: &str) -> TermId {
    let commands = ay_frontend::parse(&format!("(assert {surface})")).expect("parse");
    let [ay_frontend::command::Command::Assert(term)] = commands.as_slice() else {
        panic!("one assertion expected");
    };
    executor.raw_intern_surface(term).expect("raw intern")
}

fn respelled(executor: &mut Executor, root: TermId) -> Option<String> {
    match executor
        .respell_nullary_macro_raw_roots(vec![ReachableAuthoredSource::RawIdentity(root)])
        .as_slice()
    {
        [ReachableAuthoredSource::Parsed(parsed, source, false)] if *parsed == root => {
            Some(proof_surface_syntax::format_frontend_term(
                proof_surface_syntax::strip_frontend_annotations(source),
            ))
        }
        [ReachableAuthoredSource::RawIdentity(kept)] if *kept == root => None,
        _ => panic!("the pass may only re-spell one root or keep it"),
    }
}

const MACRO: &str = "(declare-const v0 (_ BitVec 1))\
    (define-fun one () (_ BitVec 1) #b1)\
    (assert (= v0 one))";

#[test]
fn a_raw_root_expanded_from_a_macro_row_takes_the_authored_spelling() {
    let mut executor = executor(MACRO);
    let root = raw(&mut executor, "(= v0 one)");
    assert_eq!(
        ay_proof::format_term_alethe(&executor.ctx.terms, root),
        "(= v0 #b1)"
    );
    assert_eq!(
        respelled(&mut executor, root).as_deref(),
        Some("(= v0 one)")
    );
}

/// Negative twins: a raw root that no macro row expands to, and a problem with
/// no nullary definition at all, keep the `RawIdentity` presentation.
#[test]
fn a_root_no_macro_row_expands_to_keeps_its_raw_presentation() {
    let mut executor = executor(MACRO);
    let other = raw(&mut executor, "(= v0 #b0)");
    assert_eq!(respelled(&mut executor, other), None);

    let mut plain = executor_without_macro();
    let root = raw(&mut plain, "(= v0 #b1)");
    assert_eq!(respelled(&mut plain, root), None);
}

fn executor_without_macro() -> Executor {
    executor("(declare-const v0 (_ BitVec 1))(assert (= v0 #b1))")
}

fn row(surface: &str) -> FrontendTerm {
    let commands = ay_frontend::parse(&format!("(assert {surface})")).expect("parse");
    let [Command::Assert(term)] = commands.as_slice() else {
        panic!("one assertion expected");
    };
    term.clone()
}

const BOOL_MACRO: &str = "(declare-const x (_ BitVec 4))(declare-const p Bool)\
    (define-fun lo () Bool (bvult x #x3))(assert lo)";

/// `(assert lo)` elaborates to `(bvult x #x3)`: the head comparison has no
/// authored head to compare, and the definition premise is what confines it.
#[test]
fn a_bare_bool_macro_row_is_confinable_through_its_definition() {
    let mut executor = executor(BOOL_MACRO);
    let root = raw(&mut executor, "lo");
    assert_eq!(
        ay_proof::format_term_alethe(&executor.ctx.terms, root),
        "(bvult x #b0011)"
    );
    let lo = row("lo");
    assert!(!authored_surface_is_assume_confinable(
        &executor.ctx.terms,
        root,
        &lo
    ));
    assert!(executor.authored_row_is_assume_confinable(root, &lo, &mut None));
}

/// Negative twins: a macro whose body is not the root, and a bare symbol that
/// names no macro, stay unconfinable.
#[test]
fn a_bare_symbol_row_its_definitions_do_not_bridge_is_not_confinable() {
    let mut executor = executor(BOOL_MACRO);
    let other = raw(&mut executor, "(bvult x #x2)");
    assert!(!executor.authored_row_is_assume_confinable(other, &row("lo"), &mut None));
    let root = raw(&mut executor, "lo");
    assert!(!executor.authored_row_is_assume_confinable(root, &row("p"), &mut None));
}

const NEGATED_MACRO: &str = "(declare-const x Int)(define-fun lo () Bool (< x 3))\
    (assert (not (not lo)))";

/// A macro row the printer bridges REPLACES a stale root spelling
/// (`Some(true)`), even where no head comparison admits it: `(not (not lo))`
/// over the canonical `(< x 3)`. A row that names no macro keeps the head
/// judgement and never replaces (`Some(false)`), and an odd negation of the
/// macro is refused (`None`).
#[test]
fn a_bridged_macro_row_replaces_a_stale_spelling_and_a_plain_row_does_not() {
    let mut executor = executor(NEGATED_MACRO);
    let root = raw(&mut executor, "(< x 3)");
    let mut definitions = None;
    for (surface, expected) in [
        ("(not (not lo))", Some(true)),
        ("lo", Some(true)),
        ("(< x 3)", Some(false)),
        ("(not lo)", None),
    ] {
        assert_eq!(
            executor.authored_row_confinement(root, &row(surface), &mut definitions),
            expected,
            "{surface}"
        );
    }
}

const COMPARISON_MACRO: &str = "(declare-const x Int)(declare-const r Bool)\
    (define-fun lo () Bool (>= x 3))(assert (and lo r))";

/// Raw interning canonicalizes the comparison, so no row's expansion spells
/// the root `(and (<= 3 x) r)`; the one macro row the printer bridges to it
/// is selected.
#[test]
fn a_raw_root_no_expansion_spells_takes_the_one_bridged_macro_row() {
    let mut executor = executor(COMPARISON_MACRO);
    let root = raw(&mut executor, "(and lo r)");
    assert_eq!(
        ay_proof::format_term_alethe(&executor.ctx.terms, root),
        "(and (<= 3 x) r)"
    );
    assert_eq!(
        respelled(&mut executor, root).as_deref(),
        Some("(and lo r)")
    );
}

/// Negative twins: two different macro spellings of one expansion, and a raw
/// root no macro row bridges, keep the `RawIdentity` presentation.
#[test]
fn an_ambiguous_or_unbridged_raw_root_keeps_its_raw_presentation() {
    let mut twice = executor(&format!(
        "{COMPARISON_MACRO}(define-fun lo2 () Bool (>= x 3))(assert (and lo2 r))"
    ));
    let root = raw(&mut twice, "(and lo r)");
    assert_eq!(respelled(&mut twice, root), None);
    let mut executor = executor(COMPARISON_MACRO);
    let other = raw(&mut executor, "(and (>= x 4) r)");
    assert_eq!(respelled(&mut executor, other), None);
}

/// The fallback is an exact lookup, not a search under a probe budget: with
/// more macro rows than the old 64-probe pass budget, the one row whose raw
/// re-intern is the root is still found. MEASURED with that budget: from 65
/// such rows upward the root kept its foreign canonical text and the query
/// published `(assume t1 (and (< 0 x0) (> x0 (- 5))))`, carcara `invalid`.
#[test]
fn a_raw_root_among_many_macro_rows_is_found_exactly() {
    let rows = 80;
    let mut script = String::new();
    for i in 0..rows {
        script.push_str(&format!(
            "(declare-const x{i} Int)(define-fun m{i} () Bool (> x{i} {i}))\
             (assert (and m{i} (> x{i} (- 5))))"
        ));
    }
    let mut executor = executor(&script);
    for i in [0, rows / 2, rows - 1] {
        let root = raw(&mut executor, &format!("(and m{i} (> x{i} (- 5)))"));
        assert_eq!(
            respelled(&mut executor, root).as_deref(),
            Some(format!("(and m{i} (> x{i} (- 5)))").as_str()),
            "row {i}"
        );
    }
}

const LET_MACRO: &str = "(declare-const x Int)\
    (define-fun m () Bool (let ((y (+ x 1))) (< y 0)))(assert m)";

/// A single macro row the printer can neither confine by head nor bridge
/// through its definition would publish its expanded body, so it withholds
/// the Alethe surface. Negative twins: a root that still carries the
/// authored spelling is left to the printer's own gates, and a row that
/// names no macro is never judged here.
#[test]
fn an_unconfined_macro_row_is_foreign_unless_its_root_keeps_its_spelling() {
    let mut executor = executor(LET_MACRO);
    let root = raw(&mut executor, "m");
    let m = row("m");
    assert_eq!(executor.authored_row_confinement(root, &m, &mut None), None);
    executor.last_proof_term_overrides = None;
    assert!(executor.unconfined_macro_row_is_foreign(root, &m));
    executor.last_proof_term_overrides = Some(std::iter::once((root, "m".to_string())).collect());
    assert!(!executor.unconfined_macro_row_is_foreign(root, &m));
    executor.last_proof_term_overrides = None;
    assert!(!executor.unconfined_macro_row_is_foreign(root, &row("(< (+ x 1) 0)")));
}
