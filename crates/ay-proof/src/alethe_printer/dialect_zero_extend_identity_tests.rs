// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Remaining Clean-only `zero_extend` output relies on the consumer rule
//! `dialect:expand_zero_extend` through one exact `refl` identity per
//! application. Admitted small-support circuits instead derive the identity
//! from discharged closed cases and a checked universal theorem.
//!
//! REGRESSION (2026-09-30): the complete bit-blast lane printed a `cong` from
//! the word's reference, a `define-fun` of `((_ zero_extend k) x)`, straight to
//! the blasted `concat`, folding the reliance into a congruence across two
//! heads. A step CROSSES the operator when one side of its equality, after
//! top-level `define-fun` names are expanded, is a `zero_extend` application
//! and the other is not; outside a transport step (`TRANSPORT`, whose
//! conclusion its premises fix) and an `evaluate` over closed values
//! (`closed`: pinned Carcara computes `zero_extend` on a value itself, so the
//! packed word lane's closed cases rely on no reading), every crossing step
//! must be that identity. The rule is the one
//! `ay/tests/group_soundness/external_codegen_consumer_certificates/consumer_rules/zero_extend_identity.rs`
//! applies to printed external-codegen certificates.

use super::*;

/// Rules whose conclusion its premises fix term for term, so a crossing there
/// relies on nothing; any other crossing rule fails the test (fail closed).
const TRANSPORT: [&str; 4] = ["trans", "symm", "resolution", "th_resolution"];

/// `name -> body` of every `define-fun` in `document`.
fn definitions(document: &str) -> HashMap<&str, &str> {
    document
        .lines()
        .filter(|line| line.starts_with("(define-fun "))
        .map(|line| {
            let items = top_level(line);
            (items[1], items[4])
        })
        .collect()
}

fn expand<'d>(definitions: &HashMap<&str, &'d str>, term: &'d str) -> &'d str {
    definitions.get(term).copied().unwrap_or(term)
}

/// `(k, x)` when `term` is `((_ zero_extend k) x)`.
fn zero_extend_of(term: &str) -> Option<(usize, &str)> {
    if !term.starts_with("((_ zero_extend ") {
        return None;
    }
    let [operator, operand] = top_level(term)[..] else {
        return None;
    };
    let [_, _, k] = top_level(operator)[..] else {
        return None;
    };
    Some((k.parse().ok()?, operand))
}

/// Whether `term` is a closed value pinned Carcara's `evaluate` computes: a
/// Boolean or bit-vector literal, `(_ bvN w)`, or an `@bbterm` of closed bits.
/// Deliberately narrow: anything else is not closed (fail closed).
fn closed(definitions: &HashMap<&str, &str>, term: &str) -> bool {
    let numeral = |text: &str| !text.is_empty() && text.bytes().all(|b| b.is_ascii_digit());
    let term = expand(definitions, term);
    if !term.starts_with('(') {
        return matches!(term, "true" | "false")
            || term
                .strip_prefix("#b")
                .is_some_and(|d| !d.is_empty() && d.bytes().all(|b| b == b'0' || b == b'1'))
            || term
                .strip_prefix("#x")
                .is_some_and(|d| !d.is_empty() && d.bytes().all(|b| b.is_ascii_hexdigit()));
    }
    match top_level(term)[..] {
        ["_", value, width] => value.strip_prefix("bv").is_some_and(numeral) && numeral(width),
        ["@bbterm", ref bits @ ..] => bits.iter().all(|bit| closed(definitions, bit)),
        _ => false,
    }
}

fn is_zero_word(term: &str, k: usize) -> bool {
    term.strip_prefix("#b")
        .is_some_and(|digits| digits.len() == k && digits.bytes().all(|b| b == b'0'))
        || term == format!("(_ bv0 {k})")
}

/// The crossing steps of `document`, as `(id, rule)`, after asserting that
/// each is the identity, and the number of closed `evaluate` cases.
fn crossings(case: &str, document: &str) -> (Vec<(String, String)>, usize) {
    let definitions = definitions(document);
    let mut found = Vec::new();
    let mut closed_cases = 0;
    for line in document.lines().filter(|line| line.starts_with("(step ")) {
        let items = top_level(line);
        let (id, clause) = (items[1], items[2]);
        let rule = items
            .iter()
            .position(|item| *item == ":rule")
            .map(|at| items[at + 1])
            .unwrap_or_else(|| panic!("{case}: a step without a rule: {line}"));
        let literals = top_level(clause);
        let [_, literal] = literals[..] else {
            continue;
        };
        if !literal.starts_with("(= ") {
            continue;
        }
        let [_, left, right] = top_level(literal)[..] else {
            continue;
        };
        let (left, right) = (expand(&definitions, left), expand(&definitions, right));
        let (extends, other) = (zero_extend_of(left), zero_extend_of(right));
        if extends.is_some() == other.is_some() || TRANSPORT.contains(&rule) {
            continue;
        }
        let (extension, value) = match (extends, other) {
            (Some(extension), _) => (extension, right),
            (_, Some(extension)) => (extension, left),
            (None, None) => continue,
        };
        if rule == "evaluate" && closed(&definitions, extension.1) && closed(&definitions, value) {
            closed_cases += 1;
            continue;
        }
        let (k, operand) =
            extends.unwrap_or_else(|| panic!("{case}: zero_extend on the right: {line}"));
        assert_eq!(rule, "refl", "{case}: crosses zero_extend: {line}");
        if k == 0 {
            assert_eq!(expand(&definitions, right), operand, "{case}: {line}");
        } else {
            let [head, zero, word] = top_level(right)[..] else {
                panic!("{case}: not a binary concat: {line}");
            };
            assert_eq!(head, "concat", "{case}: {line}");
            assert!(
                is_zero_word(expand(&definitions, zero), k),
                "{case}: {line}"
            );
            assert_eq!(
                expand(&definitions, word),
                expand(&definitions, operand),
                "{case}: {line}"
            );
        }
        found.push((id.to_string(), rule.to_string()));
    }
    (found, closed_cases)
}

/// The crossing steps of `document`, each asserted to be the identity.
fn identities(case: &str, document: &str) -> Vec<(String, String)> {
    crossings(case, document).0
}

/// Exact identities for remaining reliance, and checked standard Circuit output.
#[test]
fn zero_extend_has_exact_remaining_identities_and_checked_circuit_cases() {
    // The packed word lane: a 9-bit word, past the closed-case bound.
    let mut terms = TermStore::new();
    let byte = terms.mk_var("byte", Sort::bitvec(9));
    let wide = terms.mk_app(
        Symbol::indexed("zero_extend", vec![3]),
        [byte],
        Sort::bitvec(12),
    );
    let packed = terms.mk_app(Symbol::named("="), [wide, wide], Sort::Bool);
    let [_, _, steps] = packed_certificate(&terms, packed, 9);
    assert!(!identities("packed", &steps).is_empty(), "{steps}");

    // The packed-circuit lane: two extensions under one conjunction.
    let mut terms = TermStore::new();
    let mut conjuncts = Vec::new();
    for (name, amount) in [("b1", 3_u32), ("b2", 2)] {
        let b = terms.mk_var(name, Sort::bitvec(8));
        let zeros = terms.mk_bitvec(BigInt::from(0), 8);
        let source = terms.mk_app(Symbol::named("concat"), [zeros, b], Sort::bitvec(16));
        let wide = terms.mk_app(
            Symbol::indexed("zero_extend", vec![16]),
            [source],
            Sort::bitvec(32),
        );
        let count = terms.mk_bitvec(BigInt::from(amount), 32);
        let shifted = terms.mk_app(Symbol::named("bvlshr"), [wide, count], Sort::bitvec(32));
        let low = terms.mk_app(
            Symbol::indexed("extract", vec![15, 0]),
            [shifted],
            Sort::bitvec(16),
        );
        let narrow_count = terms.mk_bitvec(BigInt::from(amount), 16);
        let expected = terms.mk_app(
            Symbol::named("bvlshr"),
            [source, narrow_count],
            Sort::bitvec(16),
        );
        conjuncts.push(terms.mk_app(Symbol::named("="), [low, expected], Sort::Bool));
    }
    let both = terms.mk_app(Symbol::named("and"), conjuncts, Sort::Bool);
    // The lane proves the clause `(not root)` for the asserted `root`, here
    // the negated conjunction.
    let root = terms.mk_not_raw(both);
    let negative = terms.mk_not_raw(root);
    let printer = AlethePrinter::new(&terms);
    let (steps, report) = capture_alethe_dialect_report(|| {
        printer.format_bv_circuit_refutation(ProofId(7), &[negative])
    });
    let steps = steps.expect("the packed-circuit lane renders the same conjunction");
    let (reliance, closed_cases) = crossings("packed-circuit", &steps);
    assert!(reliance.is_empty(), "{steps}");
    assert!(
        closed_cases > 0,
        "the standard theorem retains closed evaluations"
    );
    assert!(steps.contains(":rule bind"));
    assert!(
        steps.matches(":rule forall_inst").count() >= 2,
        "both independent byte instances are checked"
    );
    assert!(report.is_pinned_spelling(), "{report:?}");
    assert!(!steps.contains(":rule hole") && !steps.contains(":rule trust"));

    // The complete bit-blast lane, with an inline reference and with one
    // behind a `define-fun` (a spelling longer than the inline bound).
    for (name, width, extra) in [("a", 4_u32, 4_u32), ("operand_named_at_length", 8, 24)] {
        let mut blast = TermStore::new();
        let a = blast.mk_var(name, Sort::bitvec(width));
        let wide = blast.mk_app(
            Symbol::indexed("zero_extend", vec![extra]),
            [a],
            Sort::bitvec(width + extra),
        );
        let narrow = blast.mk_app(
            Symbol::indexed("extract", vec![width - 1, 0]),
            [wide],
            Sort::bitvec(width),
        );
        let equality = blast.mk_app(Symbol::named("="), [narrow, a], Sort::Bool);
        let assertion = blast.mk_not_raw(equality);
        let [_, _, document] = complete_blast(&blast, assertion, &[(name, width)]);
        let found = identities(&format!("cbb-{name}"), &document);
        assert_eq!(found.len(), 1, "{document}");
        let suffix = found[0].0.rsplit_once('.').map(|(_, suffix)| suffix);
        assert_eq!(suffix, Some("zx"), "{found:?}");
    }
}

/// The packed word lane's closed cases cross the operator by `evaluate` over
/// closed values and rely on no reading: an eight-bit source prints them in
/// both dialects, and a sixteen-bit source with eight symbolic bits in the
/// pinned dialect (`zero_extend::`). Such a document relies on no identity.
#[test]
fn closed_zero_extend_cases_are_evaluations_not_reliance() {
    let mut terms = TermStore::new();
    let byte = terms.mk_var("byte", Sort::bitvec(8));
    let wide = terms.mk_app(
        Symbol::indexed("zero_extend", vec![24]),
        [byte],
        Sort::bitvec(32),
    );
    let identity = terms.mk_app(Symbol::named("="), [wide, wide], Sort::Bool);
    for dialect in [AletheDialect::Clean, AletheDialect::PinnedCarcara] {
        let [_, _, steps] =
            with_alethe_dialect(dialect, || packed_certificate(&terms, identity, 8));
        let (found, closed_cases) = crossings(&format!("byte-{dialect:?}"), &steps);
        assert!(closed_cases > 0, "{dialect:?}: no closed case in\n{steps}");
        assert_eq!(found, Vec::<(String, String)>::new(), "{dialect:?}");
    }
    let mut terms = TermStore::new();
    let byte = terms.mk_var("byte", Sort::bitvec(8));
    let zeros = terms.mk_bitvec(BigInt::from(0), 8);
    let padded = terms.mk_app(Symbol::named("concat"), [zeros, byte], Sort::bitvec(16));
    let wide = terms.mk_app(
        Symbol::indexed("zero_extend", vec![16]),
        [padded],
        Sort::bitvec(32),
    );
    let identity = terms.mk_app(Symbol::named("="), [wide, wide], Sort::Bool);
    let [_, _, steps] = with_alethe_dialect(AletheDialect::PinnedCarcara, || {
        packed_certificate(&terms, identity, 8)
    });
    let (found, closed_cases) = crossings("padded-pinned", &steps);
    assert!(closed_cases > 0, "no closed case in\n{steps}");
    assert!(found.is_empty(), "{found:?}");
}
