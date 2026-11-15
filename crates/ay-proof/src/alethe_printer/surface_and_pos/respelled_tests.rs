// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A flat `and_pos` whose conjunct the authored root spells with another
//! bit-vector literal (#screened-surface-gaps).
//!
//! `(assert (and (bvult k #x05) (forall ..) (= (g k) #x00)))`: the root keeps
//! its authored text, the projected conjunct prints canonically as
//! `(= (g k) #b00000000)`, and until this change the byte comparison refused
//! the whole export (`and_pos indexed conjunct is absent from its effective
//! source`). Pinned carcara's `and_pos` compares PARSED terms
//! (`checker/rules/tautology.rs`), and its parser builds one
//! `Constant::BitVec(0, 8)` from both literals, so the step is an ordinary
//! instance. A literal of another value or width is another term and still
//! refuses.

use super::{AlethePrintError, AlethePrinter};
use ay_core::kani_compat::DetHashMap;
use ay_core::{AletheRule, ProofId, ProofStep, Sort, Symbol, TermId, TermStore};

struct Fixture {
    terms: TermStore,
    source: TermId,
    gate: TermId,
    equality: TermId,
}

/// `(and guard (= (g k) 0))` over an 8-bit `k`.
fn fixture() -> Fixture {
    let mut terms = TermStore::new();
    let guard = terms.mk_var("respelled_guard", Sort::Bool);
    let k = terms.mk_var("k", Sort::bitvec(8));
    let applied = terms.mk_app(Symbol::named("g"), [k], Sort::bitvec(8));
    let zero = terms.mk_bitvec(0.into(), 8);
    let equality = terms.mk_app(Symbol::named("="), [applied, zero], Sort::Bool);
    let source = terms.mk_app(Symbol::named("and"), [guard, equality], Sort::Bool);
    let gate = terms.mk_not_raw(source);
    Fixture {
        terms,
        source,
        gate,
        equality,
    }
}

fn project(fixture: &Fixture, authored: &str) -> Result<String, AlethePrintError> {
    let mut overrides = DetHashMap::default();
    overrides.insert(fixture.source, authored.to_string());
    let printer = AlethePrinter::new_with_overrides(&fixture.terms, Some(&overrides));
    let step = ProofStep::Step {
        rule: AletheRule::AndPos(1),
        clause: vec![fixture.gate, fixture.equality],
        premises: Vec::new(),
        args: vec![fixture.source],
    };
    printer.format_step(&step, ProofId(3))
}

#[test]
fn a_conjunct_the_root_spells_with_another_bitvector_literal_projects() {
    let fixture = fixture();
    let printer = AlethePrinter::new(&fixture.terms);
    let canonical = printer.format_term(fixture.equality);
    assert_ne!(
        canonical, "(= (g k) #x00)",
        "the fixture must exercise a re-spelled conjunct"
    );
    for authored in [
        "(and respelled_guard (= (g k) #x00))",
        "(and respelled_guard (= (g k) (_ bv0 8)))",
    ] {
        let printed = project(&fixture, authored).expect("one parsed conjunct");
        assert_eq!(
            printed,
            format!("(step t3 (cl (not {authored}) {canonical}) :rule and_pos :args (1))")
        );
    }
}

/// NEGATIVE TWIN: another value, another width, or an operand order the
/// parser does not identify is another conjunct, and the export still refuses.
#[test]
fn a_conjunct_of_another_value_or_width_still_refuses() {
    let fixture = fixture();
    for authored in [
        "(and respelled_guard (= (g k) #x01))",
        "(and respelled_guard (= (g k) #x0000))",
        "(and respelled_guard (= #x00 (g k)))",
    ] {
        let refused = project(&fixture, authored).expect_err(authored);
        assert!(
            refused
                .to_string()
                .contains("and_pos indexed conjunct is absent from its effective source"),
            "{authored}: {refused}"
        );
    }
}
