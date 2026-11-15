// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A macro read several times in one authored assertion: its body is bridged
//! once and every later occurrence cites that step (`shared_body.rs`),
//! replayed through pinned carcara.

use super::super::shared_body::earlier_equality_step;
use super::*;

/// Nesting of `g` in the body of `m`. Five occurrences of `m`, derived
/// afresh each time, cost `2 + 5 * (DEPTH + 2)` = 262 nodes, over the
/// 256-node per-bridge allowance; shared, `2 + (DEPTH + 2) + 4` = 58.
const DEPTH: usize = 50;

/// `(g (g .. (g leaf)))`, `depth` applications deep.
fn nested_text(depth: usize, leaf: &str) -> String {
    let mut text = leaf.to_string();
    for _ in 0..depth {
        text = format!("(g {text})");
    }
    text
}

/// `(= v (f G G G G G))` for `G` = `(g .. (g z))`, `DEPTH` deep, built raw so
/// the canonical text is exactly that, plus its negation.
fn repeated_macro_contradiction(terms: &mut TermStore) -> (TermId, TermId) {
    let v = terms.mk_var("v", Sort::Int);
    let mut expanded = terms.mk_var("z", Sort::Int);
    for _ in 0..DEPTH {
        expanded = terms.mk_app(Symbol::named("g"), [expanded], Sort::Int);
    }
    let read = terms.mk_app(Symbol::named("f"), [expanded; 5], Sort::Int);
    let root = terms.mk_app(Symbol::named("="), [v, read], Sort::Bool);
    (root, terms.mk_not_raw(root))
}

/// `k` names `z`; `m` nests `g` over `k`.
fn repeated_definitions() -> HashMap<String, String> {
    let body = nested_text(DEPTH, "k");
    table(&[("k", "z"), ("m", body.as_str())])
}

#[test]
fn a_macro_read_five_times_bridges_its_body_once() {
    let mut terms = TermStore::new();
    let (root, negated) = repeated_macro_contradiction(&mut terms);
    let surface = "(= v (f m m m m m))";
    let definitions = repeated_definitions();
    assert!(nullary_definition_assume_bridge_is_supported(
        &terms,
        root,
        surface,
        &definitions
    ));
    let proof = export(&terms, root, negated, surface, Some(&definitions))
        .expect("the repeated macro is bridged within the node allowance");
    let body = nested_text(DEPTH, "k");
    let expanded = nested_text(DEPTH, "z");
    let definition = format!("(= m {body}))");
    assert_eq!(proof.matches(&definition).count(), 5, "{proof}");
    let body_bridge = format!(" (cl (= {body} {expanded})) :rule ");
    assert_eq!(proof.matches(&body_bridge).count(), 1, "{proof}");
    assert!(
        proof.contains(&format!(
            "(step t0.n.c1.c4 (cl (= m {expanded})) :rule trans :premises \
             (t0.n.c1.c4.d t0.n.c1.c0.b))"
        )),
        "{proof}"
    );
    assert!(
        !proof.contains(":rule hole") && !proof.contains(":rule trust"),
        "{proof}"
    );
    assert_carcara_valid(
        "repeated",
        &format!(
            "(set-logic QF_UFLIA)\n(declare-fun v () Int)\n(declare-fun z () Int)\n\
             (declare-fun g (Int) Int)\n(declare-fun f (Int Int Int Int Int) Int)\n\
             (define-fun k () Int z)\n(define-fun m () Int {body})\n\
             (assert {surface})\n(assert (not (= v (f {expanded} {expanded} {expanded} \
             {expanded} {expanded}))))\n(check-sat)\n"
        ),
        &proof,
    );
}

/// Negative twin: a fifth operand naming a macro whose body expands one `g`
/// short of the canonical operand is never bridged, although the four reads
/// of `m` before it share their body, and the export is exactly the one a
/// document without the table gets.
#[test]
fn a_shared_body_never_bridges_an_occurrence_its_own_definition_does_not() {
    let mut terms = TermStore::new();
    let (root, negated) = repeated_macro_contradiction(&mut terms);
    let surface = "(= v (f m m m m n))";
    let mut definitions = repeated_definitions();
    definitions.insert("n".to_string(), nested_text(DEPTH - 1, "k"));
    assert!(!nullary_definition_assume_bridge_is_supported(
        &terms,
        root,
        surface,
        &definitions
    ));
    let with_table = format!(
        "{:?}",
        export(&terms, root, negated, surface, Some(&definitions))
    );
    let without = format!("{:?}", export(&terms, root, negated, surface, None));
    assert_eq!(with_table, without);
    assert!(!with_table.contains("(= m (g"), "{with_table}");
}

/// The lookup cites only a step concluding exactly `(= left right)`, and
/// nothing once a subproof is open.
#[test]
fn the_shared_body_lookup_matches_one_exact_conclusion() {
    let lines = |text: &[&str]| {
        text.iter()
            .map(|line| (*line).to_string())
            .collect::<Vec<_>>()
    };
    let output = lines(&[
        "(assume t0.d (= m (g k)))",
        "(step t0.x (cl (= (g k) (g zz))) :rule cong :premises (t0.y))",
        "(step t0.r (cl (= (g z) (g k))) :rule symm :premises (t0.b))",
        "(step t0.w (cl (= (g k) (g z)) (not p)) :rule resolution :premises (t0.y))",
        "(step t0.b (cl (= (g k) (g z))) :rule cong :premises (t0.b.c0))",
    ]);
    // Not `t0.x` (its right operand only starts like `(g z)`), `t0.r` (the
    // other orientation) or `t0.w` (a wider clause).
    assert_eq!(
        earlier_equality_step(&output, "(g k)", "(g z)").as_deref(),
        Some("t0.b")
    );
    assert_eq!(
        earlier_equality_step(&output, "(g k)", "(g zz)").as_deref(),
        Some("t0.x")
    );
    // An `assume` is never cited, nor a line an abandoned attempt truncated.
    assert_eq!(earlier_equality_step(&output, "m", "(g k)"), None);
    assert_eq!(earlier_equality_step(&output[..4], "(g k)", "(g z)"), None);
    let mut scoped = lines(&["(anchor :step t0.s)"]);
    scoped.extend(output);
    assert_eq!(earlier_equality_step(&scoped, "(g k)", "(g z)"), None);
}
