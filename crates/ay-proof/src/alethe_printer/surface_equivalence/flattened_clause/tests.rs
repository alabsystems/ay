// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::super::{CanonicalNode, Derivation};
use super::*;
use std::process::Command;

const DECLARATIONS: &str = "(declare-const k (_ BitVec 8))\n\
    (declare-const n (_ BitVec 8))\n\
    (declare-const x (_ BitVec 8))\n\
    (declare-const e Bool)\n\
    (declare-fun g ((_ BitVec 8)) (_ BitVec 8))\n\
    (declare-fun r ((_ BitVec 8)) Bool)\n";

struct Atoms {
    terms: TermStore,
    /// `(= (g k) x)`
    equality: TermId,
    /// `(not (bvult k n))`
    negated_guard: TermId,
    /// `(r k)`
    predicate: TermId,
    /// `e`
    extra: TermId,
    /// `(bvule n k)`
    reversed: TermId,
}

fn atoms() -> Atoms {
    let mut terms = TermStore::new();
    let k = terms.mk_var("k", Sort::bitvec(8));
    let n = terms.mk_var("n", Sort::bitvec(8));
    let x = terms.mk_var("x", Sort::bitvec(8));
    let applied = terms.mk_app(Symbol::named("g"), vec![k], Sort::bitvec(8));
    let equality = terms.mk_app(Symbol::named("="), vec![applied, x], Sort::Bool);
    let guard = terms.mk_app(Symbol::named("bvult"), vec![k, n], Sort::Bool);
    let negated_guard = terms.mk_not_raw(guard);
    let predicate = terms.mk_app(Symbol::named("r"), vec![k], Sort::Bool);
    let extra = terms.mk_var("e", Sort::Bool);
    let reversed = terms.mk_app(Symbol::named("bvule"), vec![n, k], Sort::Bool);
    Atoms {
        terms,
        equality,
        negated_guard,
        predicate,
        extra,
        reversed,
    }
}

fn disjunction(terms: &mut TermStore, disjuncts: Vec<TermId>) -> TermId {
    terms.mk_app(Symbol::named("or"), disjuncts, Sort::Bool)
}

fn rules(steps: &[String]) -> Vec<String> {
    steps
        .iter()
        .map(|step| {
            let rule = step.split(":rule ").nth(1).expect("a rule");
            rule.split([' ', ')']).next().expect("a name").to_string()
        })
        .collect()
}

fn derive(terms: &TermStore, surface: &str, term: TermId) -> Option<Vec<String>> {
    let printer = AlethePrinter::new(terms);
    let canonical = printer.format_term(term);
    printer
        .printed_surface_equivalence_steps("t9.n", surface, term, &canonical)
        .map(|(steps, _)| steps)
}

/// Pinned carcara's verdict on the refutation of `(not (= surface canonical))`
/// closed by `steps`, or `None` when carcara is not on PATH (skipped, never
/// passed).
fn carcara_verdict(case: &str, surface: &str, canonical: &str, steps: &[String]) -> Option<String> {
    let negated = format!("(not (= {surface} {canonical}))");
    let problem = format!("(set-logic ALL)\n{DECLARATIONS}(assert {negated})\n(check-sat)\n");
    let proof = format!(
        "(assume h0 {negated})\n{}\n(step done (cl) :rule resolution :premises (t9.n h0))\n",
        steps.join("\n")
    );
    // Before the checker, with or without it on PATH: on a pair pinned carcara
    // misjudges its verdict is not evidence in either direction, so neither the
    // `valid` assertions nor the tampered twin's not-`valid` may pass on it.
    if let Err(misjudged) = ay_core::pinned_carcara::pinned_carcara_can_judge(&problem, &proof) {
        panic!("{case}: {misjudged}\n{proof}");
    }
    let probe = Command::new("carcara").arg("--version").output();
    if !probe.is_ok_and(|probe| probe.status.success()) {
        eprintln!("carcara not on PATH: the {case} replay is skipped");
        return None;
    }
    let scope = crate::ProblemScope::from_smtlib_source(&problem);
    if let Err(defect) = crate::check_alethe_document(&proof, &scope) {
        return Some(format!("round-trip self-check refused: {defect}\n{proof}"));
    }
    let dir = std::env::temp_dir().join(format!("ay-flattened-{}-{case}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("scratch dir");
    std::fs::write(dir.join("p.smt2"), &problem).expect("problem");
    std::fs::write(dir.join("p.alethe"), &proof).expect("proof");
    let output = Command::new("carcara")
        .arg("check")
        .arg("--expand-let-bindings")
        .arg("--")
        .arg(dir.join("p.alethe"))
        .arg(dir.join("p.smt2"))
        .output()
        .expect("run carcara");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let verdict = stdout.lines().last().unwrap_or("").trim().to_string();
    if verdict == "valid" {
        let _ = std::fs::remove_dir_all(&dir);
    }
    let stderr = String::from_utf8_lossy(&output.stderr);
    Some(format!(
        "{verdict}\n{stderr}\nkept: {}\n{proof}",
        dir.display()
    ))
}

/// NEGATIVE CONTROL: the replay refuses, before the checker runs, a
/// derivation resting on an `evaluate` step pinned carcara misjudges (the
/// shape of `ay_core::pinned_carcara::FALSE_VALID_CONTROL_PROOF`, which it
/// answers `valid` for), so no assertion above can pass on one.
#[test]
#[should_panic(expected = "is not evidence")]
fn the_carcara_replay_refuses_a_document_pinned_carcara_misjudges() {
    carcara_verdict(
        "false_valid_control",
        "(bvsge #xf #xe)",
        "false",
        &["(step t9.n (cl (= (bvsge #xf #xe) false)) :rule evaluate)".to_string()],
    );
}

/// Derives `(= surface canonical)`, requires `rules` among its steps and no
/// step outside the stock inventory, and requires pinned carcara to check the
/// refutation of its negation as a literal `valid`.
fn assert_checked(case: &str, surface: &str, term: TermId, terms: &TermStore, rules_used: &[&str]) {
    let canonical = AlethePrinter::new(terms).format_term(term);
    let steps = derive(terms, surface, term).unwrap_or_else(|| panic!("{case}: no derivation"));
    let last = steps.last().expect("a derivation");
    assert!(
        last.starts_with(&format!(
            "(step t9.n (cl (= {surface} {canonical})) :rule resolution"
        )),
        "{case}: {last}"
    );
    let used = rules(&steps);
    for rule in rules_used {
        assert!(
            used.iter().any(|used| used == rule),
            "{case}: {rule} missing: {steps:#?}"
        );
    }
    for rule in ["hole", "trust", "not_simplify"] {
        assert!(
            !used.iter().any(|used| used == rule),
            "{case}: {rule} used: {steps:#?}"
        );
    }
    if let Some(verdict) = carcara_verdict(case, surface, &canonical, &steps) {
        assert_eq!(
            verdict.lines().next().unwrap_or(""),
            "valid",
            "{case}: {verdict}"
        );
    }
}

/// `(not (and g (not E)))` against `(or E (not g))`: De Morgan with the double
/// negation read as its core, every leaf paired with its exact disjunct.
#[test]
fn negated_conjunction_derives_its_canonical_disjunction() {
    let mut atoms = atoms();
    let canonical = disjunction(&mut atoms.terms, vec![atoms.equality, atoms.negated_guard]);
    assert_checked(
        "negated_conjunction",
        "(not (and (bvult k n) (not (= (g k) x))))",
        canonical,
        &atoms.terms,
        &[
            "and_neg",
            "and_pos",
            "or_neg",
            "or_pos",
            "equiv_neg1",
            "equiv_neg2",
        ],
    );
}

/// `(=> G (or C R))` against the flat `(or C R (not G))` (the reviewer's
/// `f01`), a curried `(=> G (=> R C))`, and `(not (and G (not (or C R))))`.
#[test]
fn nested_implications_and_disjunctions_flatten() {
    let mut atoms = atoms();
    let canonical = disjunction(
        &mut atoms.terms,
        vec![atoms.equality, atoms.predicate, atoms.negated_guard],
    );
    assert_checked(
        "implication_over_disjunction",
        "(=> (bvult k n) (or (= (g k) x) (r k)))",
        canonical,
        &atoms.terms,
        &[
            "implies_pos",
            "implies_neg1",
            "implies_neg2",
            "or_pos",
            "or_neg",
        ],
    );
    // A curried implication over a re-spelled guard (the reviewer's `f03`);
    // over the canonical literals themselves it is the `implies_pos` chain's.
    let negated_predicate = atoms.terms.mk_not_raw(atoms.predicate);
    let negated_reversed = atoms.terms.mk_not_raw(atoms.reversed);
    let curried = disjunction(
        &mut atoms.terms,
        vec![atoms.equality, negated_predicate, negated_reversed],
    );
    assert_checked(
        "curried_implication",
        "(=> (bvuge k n) (=> (r k) (= (g k) x)))",
        curried,
        &atoms.terms,
        &[
            "implies_pos",
            "implies_neg1",
            "implies_neg2",
            "pbblast_bvuge",
        ],
    );
    let exact_curried = disjunction(
        &mut atoms.terms,
        vec![atoms.equality, negated_predicate, atoms.negated_guard],
    );
    assert_eq!(
        derive(
            &atoms.terms,
            "(=> (bvult k n) (=> (r k) (= (g k) x)))",
            exact_curried
        ),
        None
    );
    // `(not (and G (not (or C R))))` (the reviewer's `f04`).
    assert_checked(
        "negated_conjunction_over_negated_disjunction",
        "(not (and (bvult k n) (not (or (= (g k) x) (r k)))))",
        canonical,
        &atoms.terms,
        &["and_neg", "and_pos", "or_pos", "or_neg"],
    );
}

/// A repeated authored leaf shares the one disjunct elaboration kept (the
/// reviewer's `n11`), and a re-spelled leaf pairs through a derived equality.
#[test]
fn repeated_and_respelled_leaves_pair() {
    let mut atoms = atoms();
    let canonical = disjunction(&mut atoms.terms, vec![atoms.equality, atoms.negated_guard]);
    assert_checked(
        "repeated_leaf",
        "(not (and (bvult k n) (bvult k n) (not (= (g k) x))))",
        canonical,
        &atoms.terms,
        &["and_neg", "and_pos"],
    );
    let negated_reversed = atoms.terms.mk_not_raw(atoms.reversed);
    let respelled = disjunction(&mut atoms.terms, vec![atoms.equality, negated_reversed]);
    assert_checked(
        "respelled_leaves",
        "(not (and (bvuge k n) (not (= x (g k)))))",
        respelled,
        &atoms.terms,
        &["equiv_pos1", "equiv_pos2", "pbblast_bvuge", "refl"],
    );
}

/// A disjunction reordered and regrouped over re-spelled literals (the shape
/// of a universal over `(or (= (g i) #x01) (or (r i) (not (bvult i #x05))))`,
/// holed at 938ec0327) derives, and so does one repeating a literal; one that
/// only regroups the canonical literals one to one, or a double-negation-free
/// negated conjunction over them, is left to its consumers, which already
/// print it.
#[test]
fn regrouped_disjunctions_derive_only_over_respelled_literals() {
    let mut atoms = atoms();
    let negated_reversed = atoms.terms.mk_not_raw(atoms.reversed);
    let respelled = disjunction(
        &mut atoms.terms,
        vec![atoms.equality, atoms.predicate, negated_reversed],
    );
    assert_checked(
        "regrouped_respelled_disjunction",
        "(or (not (bvuge k n)) (or (r k) (= x (g k))))",
        respelled,
        &atoms.terms,
        &["or_pos", "or_neg", "equiv_pos1", "equiv_pos2"],
    );
    let exact = disjunction(
        &mut atoms.terms,
        vec![atoms.equality, atoms.predicate, atoms.negated_guard],
    );
    for surface in [
        "(or (not (bvult k n)) (r k) (= (g k) x))",
        "(or (= (g k) x) (or (r k) (not (bvult k n))))",
    ] {
        assert_eq!(derive(&atoms.terms, surface, exact), None, "{surface}");
    }
    // A negated conjunction over the canonical literals, flat or nested, up to
    // equality orientation: the `or_pos` De Morgan repair prints it.
    let negated_equality = atoms.terms.mk_not_raw(atoms.equality);
    let de_morgan = disjunction(
        &mut atoms.terms,
        vec![negated_equality, atoms.negated_guard],
    );
    for surface in [
        "(not (and (= (g k) x) (bvult k n)))",
        "(not (and (= x (g k)) (bvult k n)))",
    ] {
        assert_eq!(derive(&atoms.terms, surface, de_morgan), None, "{surface}");
    }
    let wider = disjunction(
        &mut atoms.terms,
        vec![negated_equality, atoms.negated_guard, negated_reversed],
    );
    assert_eq!(
        derive(
            &atoms.terms,
            "(not (and (and (= (g k) x) (bvult k n)) (bvule n k)))",
            wider
        ),
        None
    );
    // A repeated literal elaboration dropped is not a regrouping.
    assert_checked(
        "repeated_disjunct",
        "(or (r k) (= (g k) x) (not (bvult k n)) (r k))",
        exact,
        &atoms.terms,
        &["or_pos", "or_neg"],
    );
    // A double negation is a connective of its own, not a regrouping.
    assert_checked(
        "regrouped_double_negation",
        "(or (r k) (= (g k) x) (not (not (not (bvult k n)))))",
        exact,
        &atoms.terms,
        &["or_pos", "or_neg"],
    );
}

/// NEGATIVE TWINS: a clause whose leaves are not exactly the canonical
/// disjuncts is no equivalence this schema may claim.
#[test]
fn clauses_that_are_not_the_disjunction_decline() {
    let mut atoms = atoms();
    let canonical = disjunction(&mut atoms.terms, vec![atoms.equality, atoms.negated_guard]);
    for surface in [
        // The consequent under the wrong polarity.
        "(not (and (bvult k n) (= (g k) x)))",
        // Another guard.
        "(not (and (bvult n k) (not (= (g k) x))))",
        // An extra leaf no disjunct claims.
        "(not (and (bvult k n) (not (= (g k) x)) (bvult k k)))",
        // A negated disjunction is a conjunction, not this disjunction.
        "(not (or (bvult k n) (not (= (g k) x))))",
        // An n-ary implication is not unfolded.
        "(=> (bvult k n) (r k) (= (g k) x))",
    ] {
        assert_eq!(derive(&atoms.terms, surface, canonical), None, "{surface}");
    }
    // Fewer leaves than disjuncts: every leaf pairs, one disjunct is left over.
    let wider = disjunction(
        &mut atoms.terms,
        vec![atoms.equality, atoms.negated_guard, atoms.extra],
    );
    assert_eq!(
        derive(
            &atoms.terms,
            "(not (and (bvult k n) (not (= (g k) x))))",
            wider
        ),
        None
    );
    // The flattened implication over a canonical term that is no disjunction.
    let conjunction = atoms.terms.mk_app(
        Symbol::named("and"),
        vec![atoms.equality, atoms.negated_guard],
        Sort::Bool,
    );
    assert_eq!(
        derive(&atoms.terms, "(=> (bvult k n) (= (g k) x))", conjunction),
        None
    );
}

/// A first attempt never admits this schema, so a pair an established schema
/// relates keeps its established derivation byte-for-byte.
#[test]
fn the_first_attempt_does_not_admit_the_flattening() {
    let mut atoms = atoms();
    let canonical = disjunction(&mut atoms.terms, vec![atoms.equality, atoms.negated_guard]);
    let printer = AlethePrinter::new(&atoms.terms);
    let text = printer.format_term(canonical);
    let node = CanonicalNode {
        term: canonical,
        text: &text,
    };
    let surface = "(not (and (bvult k n) (not (= (g k) x))))";
    let mut first = Derivation::default();
    assert!(!printer.derive_printed_equivalence("t9.n", surface, node, 0, &mut first));
    assert_eq!(first.steps.as_slice(), &[] as &[String]);
    let mut second = Derivation {
        tier: SchemaTier::Extended,
        ..Derivation::default()
    };
    assert!(printer.derive_printed_equivalence("t9.n", surface, node, 0, &mut second));
}

/// A tampered derivation is refused by pinned carcara, so the replay above
/// checks the schema rather than passing whatever it is handed.
#[test]
fn pinned_carcara_refuses_a_tampered_flattening() {
    let mut atoms = atoms();
    let canonical = disjunction(&mut atoms.terms, vec![atoms.equality, atoms.negated_guard]);
    let text = AlethePrinter::new(&atoms.terms).format_term(canonical);
    let surface = "(not (and (bvult k n) (not (= (g k) x))))";
    let steps = derive(&atoms.terms, surface, canonical).expect("a derivation");
    let mut dropped = steps.clone();
    // Without the backward `or_pos` the backward resolution has no conflict.
    dropped.retain(|step| !step.starts_with("(step t9.n.ub0 "));
    let dropped: Vec<String> = dropped
        .into_iter()
        .map(|step| step.replace(" t9.n.ub0 ", " ").replace("(t9.n.ub0 ", "("))
        .collect();
    if let Some(verdict) = carcara_verdict("tampered", surface, &text, &dropped) {
        assert_ne!(verdict.lines().next().unwrap_or(""), "valid", "{verdict}");
    }
}
