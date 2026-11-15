// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::{kani_compat::DetHashMap, ProofStep, Sort, TermStore};

struct Fixture {
    terms: TermStore,
    source: TermId,
    clause: Vec<TermId>,
    overrides: DetHashMap<TermId, String>,
}

fn fixture(negate: [bool; 2]) -> Fixture {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let c = terms.mk_var("c", Sort::Bool);
    let inputs = [a, b]
        .into_iter()
        .zip(negate)
        .map(
            |(term, negate)| {
                if negate {
                    terms.mk_not(term)
                } else {
                    term
                }
            },
        )
        .collect();
    let antecedent = terms.mk_and(inputs);
    let source = terms.mk_implies(antecedent, c);
    let TermData::App(_, operands) = terms.get(source) else {
        panic!("expected flattened OR");
    };
    assert_eq!(operands.len(), 3);
    let mut clause = operands.clone();
    clause.push(terms.mk_not_raw(source));
    let spell = |name, negate| {
        if negate {
            format!("(not {name})")
        } else {
            format!("{name}")
        }
    };
    let surface = format!(
        "(=> (and {} {}) c)",
        spell("a", negate[0]),
        spell("b", negate[1])
    );
    let mut overrides = DetHashMap::default();
    overrides.insert(source, surface);
    Fixture {
        terms,
        source,
        clause,
        overrides,
    }
}

fn print(f: &Fixture) -> Result<String, AlethePrintError> {
    AlethePrinter::new_with_overrides(&f.terms, Some(&f.overrides)).format_step(
        &ProofStep::Step {
            rule: AletheRule::OrPos(0),
            clause: f.clause.clone(),
            premises: vec![],
            args: vec![f.source],
        },
        ProofId(14),
    )
}

#[test]
fn flattened_implication_derives_all_antecedent_polarities_and_clause_orders() {
    for negate in [[false, false], [true, false], [false, true], [true, true]] {
        let mut f = fixture(negate);
        for _ in 0..4 {
            let text = print(&f).expect("exact source implication must have a derivation");
            assert_eq!(text.matches(":rule implies_pos").count(), 1, "{text}");
            assert_eq!(text.matches(":rule and_neg").count(), 1, "{text}");
            assert_eq!(
                text.matches(":rule not_not").count(),
                negate.into_iter().filter(|n| *n).count(),
                "{text}"
            );
            assert!(!text.contains(":rule or_pos"), "{text}");
            assert!(!text.contains(":rule hole"), "{text}");
            let printer = AlethePrinter::new_with_overrides(&f.terms, Some(&f.overrides));
            assert!(
                text.contains(&format!(
                    "(step t14 {} :rule resolution",
                    printer.format_clause(&f.clause)
                )),
                "{text}"
            );
            f.clause.rotate_left(1);
        }
    }
}

#[test]
fn flattened_implication_rejects_changed_missing_and_duplicate_internal_literals() {
    for mutation in 0..4 {
        let mut f = fixture([true, true]);
        match mutation {
            0 => {
                f.clause[0] = f.terms.mk_var("different", Sort::Bool);
            }
            1 => {
                f.clause.pop();
            }
            2 => {
                f.clause[0] = f.clause[1];
            }
            _ => {
                let end = f.clause.len() - 1;
                f.clause[end] = f.source;
            }
        }
        assert!(matches!(
            print(&f),
            Err(AlethePrintError::InvalidSurfaceStep { .. })
        ));
    }
}

#[test]
fn flattened_implication_rejects_changed_authored_literals_and_arity() {
    for surface in [
        "(=> (and (not a) (not b)) a)",
        "(=> (and (not a) b) c)",
        "(=> (and (not a) (not a)) c)",
        "(=> (and (not a) (not b) d) c)",
    ] {
        let mut f = fixture([true, true]);
        f.overrides.insert(f.source, surface.to_string());
        assert!(matches!(
            print(&f),
            Err(AlethePrintError::InvalidSurfaceStep { .. })
        ));
    }
}

#[test]
fn flattened_implication_rejects_premises_and_extra_source_arguments() {
    let f = fixture([true, true]);
    for (premises, args) in [
        (vec![ProofId(0)], vec![f.source]),
        (vec![], vec![f.source, f.source]),
    ] {
        let printer = AlethePrinter::new_with_overrides(&f.terms, Some(&f.overrides));
        let result = printer.format_step(
            &ProofStep::Step {
                rule: AletheRule::OrPos(0),
                clause: f.clause.clone(),
                premises,
                args,
            },
            ProofId(14),
        );
        assert!(matches!(
            result,
            Err(AlethePrintError::InvalidSurfaceStep { .. })
        ));
    }
}

#[test]
fn flattened_implication_rejects_oversized_surface_conjunction() {
    let mut f = fixture([true, true]);
    f.overrides.insert(
        f.source,
        format!(
            "(=> (and {}) c)",
            vec!["a"; PRINTED_NESTING_NODE_BUDGET + 1].join(" ")
        ),
    );
    assert!(matches!(
        print(&f),
        Err(AlethePrintError::InvalidSurfaceStep { .. })
    ));
}

#[test]
fn flattened_implication_leaves_ordinary_nary_or_unchanged() {
    let mut f = fixture([true, true]);
    f.overrides.clear();
    let text = print(&f).expect("an ordinary OR does not enter the implication bridge");
    assert_eq!(text.matches(":rule or_pos").count(), 1, "{text}");
    assert_eq!(text.lines().count(), 1, "{text}");
}
