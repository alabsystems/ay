// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Strict-mode coverage for sub-schema (P), the PREDICATE-conclusion
//! congruence explanation.
//!
//! Three layers, in the order the soundness argument needs them:
//!
//! 1. **Adversarial negatives.** Every one names a CONCRETE falsifying
//!    assignment and CHECKS it in-test with [`falsifying_model`] before
//!    asserting the decline, so a decline can never be argued away as
//!    over-caution and a fixture can never come back green on a clause that was
//!    valid all along.
//! 2. **Exhaustive sweeps** over two bounded alphabets. Every clause in the box
//!    is decided by BOTH the recognizer and [`falsifying_model`], an
//!    INDEPENDENT decision procedure that shares no code with it: the
//!    recognizer SATURATES a congruence closure, the evaluator ENUMERATES every
//!    two-valued quotient structure over the clause's own sub-terms. The sweeps
//!    assert `accept => valid` on the whole box, not only on hand-picked cases.
//! 3. **A guard-mutation ledger** ([`GUARD_MUTATION_LEDGER`]) naming, for each
//!    guard in the validator, the test that goes red when it is deleted.

use super::{recognize_euf_polarity_congruence, validate_euf_polarity_congruence};
use crate::checker::{recognize_euf_congruence_explanation, validate_step, ProofCheckError};
use ay_core::{ProofId, ProofStep, Sort, TermData, TermId, TermStore, TheoryLemmaKind};

// ===== fixture helpers =====

fn mk_eq(terms: &mut TermStore, lhs: TermId, rhs: TermId) -> TermId {
    terms.mk_app(ay_core::Symbol::named("="), vec![lhs, rhs], Sort::Bool)
}

fn mk_fun(terms: &mut TermStore, name: &str, args: Vec<TermId>, sort: Sort) -> TermId {
    terms.mk_app(ay_core::Symbol::named(name), args, sort)
}

fn mk_or(terms: &mut TermStore, args: Vec<TermId>) -> TermId {
    terms.mk_app(ay_core::Symbol::named("or"), args, Sort::Bool)
}

fn neq(terms: &mut TermStore, lhs: TermId, rhs: TermId) -> TermId {
    let eq = mk_eq(terms, lhs, rhs);
    terms.mk_not_raw(eq)
}

/// Run the clause through the STRICT checker, exactly as `check_proof_strict`
/// would for a recorded `TheoryLemma` of this kind.
fn strict(terms: &TermStore, clause: Vec<TermId>) -> Result<(), ProofCheckError> {
    let step = ProofStep::TheoryLemma {
        theory: "EUF".to_string(),
        clause,
        farkas: None,
        kind: TheoryLemmaKind::EufCongruenceExplanation,
        lia: None,
    };
    let mut derived = Vec::new();
    validate_step(terms, &mut derived, ProofId(0), &step, true, None)
}

/// Whether sub-schema (P) accepts, with the dispatch invariant asserted on
/// every call: the shared kind's strict arm must accept exactly the union of
/// its two sub-schemas, so neither the classifier nor the checker can label a
/// clause the other refuses.
fn accepts(terms: &TermStore, clause: &[TermId]) -> bool {
    let polarity = recognize_euf_polarity_congruence(terms, clause);
    let equality = recognize_euf_congruence_explanation(terms, clause);
    assert_eq!(
        strict(terms, clause.to_vec()).is_ok(),
        equality || polarity,
        "the strict dispatch must accept exactly (E) or (P)"
    );
    polarity
}

// ===== the independent evaluator =====
//
// A ground Boolean clause `L_1 ∨ .. ∨ L_k` is INVALID exactly when some
// structure falsifies every literal. Over the clause's own sub-terms a
// structure is fully described by
//
//   * a PARTITION of the non-`Bool` sub-terms (which of them denote the same
//     element), and
//   * a TRUTH VALUE for each `Bool` sub-term (`Bool` has exactly two elements,
//     so two `Bool` terms are equal precisely when they agree),
//
// subject to three realizability conditions: an equality atom is true exactly
// when its sides land in one class; a `not` is the negation of its argument;
// and two applications of the same symbol at the same arity whose arguments
// land in the same classes must themselves land in the same class. Any
// assignment meeting all three IS realized — take the classes as the domain and
// read each symbol's table off the applications.
//
// Enumerating every such assignment therefore DECIDES validity. That is a
// completely different procedure from the recognizer's bottom-up saturation and
// shares no code with it: no union-find, no signature table, no
// `flatten_or_clause`, no `strip_not`, no `decode_eq`.
//
// Every alphabet handed to it is built only from variables and applications of
// symbols used at ONE arity and ONE result sort, so its unsorted reading of a
// symbol coincides with the many-sorted structures.

/// Sub-terms in post-order, descending through applications and `not` only.
fn collect_subterms(terms: &TermStore, roots: &[TermId]) -> Vec<TermId> {
    fn walk(
        terms: &TermStore,
        term: TermId,
        seen: &mut std::collections::BTreeSet<TermId>,
        order: &mut Vec<TermId>,
    ) {
        if !seen.insert(term) {
            return;
        }
        match terms.get(term) {
            TermData::App(_, args) => {
                for arg in args.clone() {
                    walk(terms, arg, seen, order);
                }
            }
            TermData::Not(inner) => walk(terms, *inner, seen, order),
            _ => {}
        }
        order.push(term);
    }
    let mut order = Vec::new();
    let mut seen = std::collections::BTreeSet::new();
    for &root in roots {
        walk(terms, root, &mut seen, &mut order);
    }
    order
}

/// Enumerate every partition of `0..n` as a restricted growth string.
fn for_each_partition(n: usize, mut visit: impl FnMut(&[usize]) -> bool) {
    fn rec(
        index: usize,
        n: usize,
        used: usize,
        blocks: &mut Vec<usize>,
        visit: &mut impl FnMut(&[usize]) -> bool,
    ) -> bool {
        if index == n {
            return visit(blocks);
        }
        for block in 0..=used {
            blocks.push(block);
            let keep = rec(
                index + 1,
                n,
                if block == used { used + 1 } else { used },
                blocks,
                visit,
            );
            blocks.pop();
            if !keep {
                return false;
            }
        }
        true
    }
    let mut blocks = Vec::with_capacity(n);
    rec(0, n, 0, &mut blocks, &mut visit);
}

/// One pre-decoded sub-term of the evaluator's own reading of the clause.
#[derive(Clone)]
enum Node {
    App(String, Vec<usize>),
    Not(usize),
    Leaf,
}

/// Whether `(class, truth)` describes a real structure: an equality atom is
/// true exactly when its sides share a class, a `not` is the negation of its
/// argument, and two applications of the same symbol at the same arity whose
/// arguments share classes share a class themselves.
fn realizable(nodes: &[Node], class: &[usize], truth: &[bool]) -> bool {
    for (index, node) in nodes.iter().enumerate() {
        match node {
            Node::App(name, args) if name == "=" && args.len() == 2 => {
                if truth[index] != (class[args[0]] == class[args[1]]) {
                    return false;
                }
            }
            Node::Not(inner) => {
                if truth[index] == truth[*inner] {
                    return false;
                }
            }
            _ => {}
        }
    }
    for (i, left) in nodes.iter().enumerate() {
        let Node::App(name_i, args_i) = left else {
            continue;
        };
        for (j, right) in nodes.iter().enumerate().skip(i + 1) {
            let Node::App(name_j, args_j) = right else {
                continue;
            };
            if name_i != name_j || args_i.len() != args_j.len() {
                continue;
            }
            let same = args_i
                .iter()
                .zip(args_j.iter())
                .all(|(&a, &b)| class[a] == class[b]);
            if same && class[i] != class[j] {
                return false;
            }
        }
    }
    true
}

/// The first structure falsifying every literal, rendered as a readable
/// listing, or `None` when the clause is valid.
fn falsifying_model(terms: &TermStore, literals: &[TermId]) -> Option<String> {
    let subterms = collect_subterms(terms, literals);
    let position: std::collections::BTreeMap<TermId, usize> = subterms
        .iter()
        .enumerate()
        .map(|(index, &term)| (term, index))
        .collect();
    let boolean: Vec<bool> = subterms
        .iter()
        .map(|&term| terms.sort(term) == &Sort::Bool)
        .collect();
    let element: Vec<usize> = (0..subterms.len()).filter(|&i| !boolean[i]).collect();
    let bools: Vec<usize> = (0..subterms.len()).filter(|&i| boolean[i]).collect();
    assert!(
        bools.len() <= 20 && element.len() <= 10,
        "the independent evaluator is only run on small alphabets"
    );
    let nodes: Vec<Node> = subterms
        .iter()
        .map(|&term| match terms.get(term) {
            TermData::App(symbol, args) => Node::App(
                symbol.name().to_string(),
                args.iter().map(|arg| position[arg]).collect(),
            ),
            TermData::Not(inner) => Node::Not(position[inner]),
            _ => Node::Leaf,
        })
        .collect();

    let mut found = None;
    for_each_partition(element.len(), |blocks| {
        // Element classes; `Bool` nodes get their class from their truth value,
        // shifted past every element class so the two never collide.
        let shift = element.len() + 1;
        for mask in 0u32..(1u32 << bools.len()) {
            let mut class = vec![usize::MAX; subterms.len()];
            let mut truth = vec![false; subterms.len()];
            for (slot, &index) in element.iter().enumerate() {
                class[index] = blocks[slot];
            }
            for (slot, &index) in bools.iter().enumerate() {
                let value = (mask >> slot) & 1 == 1;
                truth[index] = value;
                class[index] = shift + usize::from(value);
            }
            if !realizable(&nodes, &class, &truth) {
                continue;
            }
            if literals.iter().any(|literal| truth[position[literal]]) {
                continue;
            }
            let mut lines: Vec<String> = Vec::new();
            for (index, &term) in subterms.iter().enumerate() {
                lines.push(if boolean[index] {
                    format!("#{}:={}", term.0, truth[index])
                } else {
                    format!("#{}:~{}", term.0, class[index])
                });
            }
            found = Some(lines.join(" "));
            return false;
        }
        true
    });
    found
}

fn is_valid(terms: &TermStore, literals: &[TermId]) -> bool {
    falsifying_model(terms, literals).is_none()
}

/// Assert the clause really is FALSIFIABLE (so the decline below is not
/// over-caution), naming the model the evaluator found.
fn refuted_at(terms: &TermStore, literals: &[TermId]) -> String {
    falsifying_model(terms, literals).expect("this negative's clause must be falsifiable")
}

// ===== the measured population =====

/// Build the measured B-method `mem` explanation. `extra` adds the two bare
/// `Bool` argument literals of the ten-literal variant.
fn clearsy_clause(terms: &mut TermStore, extra: bool) -> Vec<TermId> {
    let set = Sort::Uninterpreted("SET".to_string());
    let boolean = terms.mk_var("BOOL", set.clone());
    let g179 = terms.mk_var("g179", set.clone());
    let g187 = terms.mk_var("g187", set.clone());
    let g222 = terms.mk_var("g222", set.clone());
    let g266 = terms.mk_var("g266", set.clone());
    let g404 = terms.mk_var("g404", set.clone());
    let true_elem = terms.mk_var("TRUE", set.clone());
    let arrow = mk_fun(terms, "-->", vec![boolean, boolean], set.clone());
    let (subject, witness) = if extra {
        (
            terms.mk_var("b810", Sort::Bool),
            terms.mk_var("b811", Sort::Bool),
        )
    } else {
        let shared = terms.mk_var("b794", Sort::Bool);
        (shared, shared)
    };
    let bool_subject = mk_fun(terms, "bool", vec![subject], set.clone());
    let bool_witness = mk_fun(terms, "bool", vec![witness], set);
    let mem_premise = mk_fun(terms, "mem", vec![g266, g187], Sort::Bool);
    let mem_unused = mk_fun(terms, "mem", vec![g222, arrow], Sort::Bool);
    let conclusion = mk_fun(terms, "mem", vec![bool_witness, g404], Sort::Bool);
    let not_premise = terms.mk_not_raw(mem_premise);
    let not_unused = terms.mk_not_raw(mem_unused);
    let mut clause = vec![
        neq(terms, boolean, g179),
        neq(terms, g179, g187),
        not_unused,
        not_premise,
        neq(terms, true_elem, g266),
        neq(terms, boolean, g404),
    ];
    if extra {
        clause.push(subject);
        clause.push(witness);
    }
    clause.push(neq(terms, true_elem, bool_subject));
    clause.push(conclusion);
    clause
}

/// The measured eight-literal shape: `mem(g266, g187)` and the conclusion are
/// congruent through TWO equality chains, and one `mem` literal is unused.
#[test]
fn accepts_the_measured_mem_congruence_shape() {
    let mut terms = TermStore::new();
    let clause = clearsy_clause(&mut terms, false);
    assert!(accepts(&terms, &clause));
    // The equality schema declines it — this clause is genuinely new reach.
    assert!(!recognize_euf_congruence_explanation(&terms, &clause));
}

/// The measured TEN-literal variant, whose two congruent `mem` atoms are
/// related only through the FALSE class: `b810` and `b811` are two distinct
/// `Bool` atoms the falsifying model must make false, hence equal.
#[test]
fn accepts_the_measured_ten_literal_variant() {
    let mut terms = TermStore::new();
    let clause = clearsy_clause(&mut terms, true);
    assert!(accepts(&terms, &clause));
    assert!(!recognize_euf_congruence_explanation(&terms, &clause));
}

/// The packed `(cl (or ..))` form the producer records is accepted identically.
#[test]
fn accepts_the_packed_form_of_the_measured_shape() {
    let mut terms = TermStore::new();
    let clause = clearsy_clause(&mut terms, false);
    let packed = mk_or(&mut terms, clause);
    assert!(accepts(&terms, &[packed]));
}

/// PRINTER: a clause of the NEW shape publishes the honest `hole` and never
/// names a rule an external checker would have to take on faith. Sub-schema (P)
/// shares the kind, hence the kind's wire lowering, so this pins that the new
/// reach did not smuggle a rule name onto the wire.
#[test]
fn the_new_shape_prints_the_honest_hole() {
    let mut terms = TermStore::new();
    let set = Sort::Uninterpreted("SET".to_string());
    let a = terms.mk_var("wa", set.clone());
    let b = terms.mk_var("wb", set.clone());
    let premise = mk_fun(&mut terms, "mem", vec![a, a], Sort::Bool);
    let conclusion = mk_fun(&mut terms, "mem", vec![b, b], Sort::Bool);
    let hypothesis = neq(&mut terms, a, b);
    let not_premise = terms.mk_not_raw(premise);
    let clause = vec![hypothesis, not_premise, conclusion];
    assert!(accepts(&terms, &clause));
    let step = ProofStep::TheoryLemma {
        theory: "EUF".to_string(),
        clause,
        farkas: None,
        kind: TheoryLemmaKind::EufCongruenceExplanation,
        lia: None,
    };
    let printer = crate::alethe_printer::AlethePrinter::new(&terms);
    let text = printer
        .format_step(&step, ProofId(1))
        .expect("a polarity congruence explanation renders as an honest unproved step");
    assert_eq!(
        text,
        "(step t1 (cl (not (= wa wb)) (not (mem wa wa)) (mem wb wb)) :rule hole)"
    );
    assert!(!text.contains("euf_") && !text.contains(":rule trust") && !text.contains(":args"));
}

#[cfg(test)]
#[path = "euf_polarity_congruence_tests/negatives.rs"]
mod negatives;

#[cfg(test)]
#[path = "euf_polarity_congruence_tests/sweeps.rs"]
mod sweeps;
