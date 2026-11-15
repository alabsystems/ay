// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::kani_compat::DetHashMap;

struct Fixture {
    terms: TermStore,
    shared: TermId,
    left: TermId,
    right: TermId,
    root: TermId,
    literal: TermId,
}

fn fixture() -> Fixture {
    let mut terms = TermStore::new();
    let shared = terms.mk_var("t", Sort::bitvec(8));
    let five = terms.mk_bitvec(5.into(), 8);
    let six = terms.mk_bitvec(6.into(), 8);
    let left = terms.mk_app(Symbol::named("="), [shared, five], Sort::Bool);
    let right = terms.mk_app(Symbol::named("="), [six, shared], Sort::Bool);
    let root = terms.mk_app(Symbol::named("and"), [left, right], Sort::Bool);
    let literal = terms.mk_not_raw(root);
    Fixture {
        terms,
        shared,
        left,
        right,
        root,
        literal,
    }
}

#[test]
fn child_equality_overrides_cannot_change_the_decoded_endpoints() {
    let f = fixture();
    for (target, surface) in [
        // Equivalent, but `eq_transitive` does not prove this zero-add bridge.
        (f.left, "(= (bvadd t #x00) #x05)"),
        (f.right, "(= #x06 (bvadd t #x00))"),
        (f.left, "(= u #x05)"),
        (f.right, "(= #x06 u)"),
        (f.left, "(= t #x06)"),
        (f.right, "(= #x05 t)"),
        (f.left, "(not (= t #x05))"),
        (f.left, "(= t #x05 #x05)"),
    ] {
        let overrides = [(target, surface.to_string())].into_iter().collect();
        let printer = AlethePrinter::new_with_overrides(&f.terms, Some(&overrides));
        // The former root-only guard accepts each case: the mismatch lives
        // inside a child equality, not between the root and its children.
        assert_eq!(
            printer.format_term(f.root),
            format!(
                "(and {} {})",
                printer.format_term(f.left),
                printer.format_term(f.right)
            ),
            "{surface}"
        );
        assert!(
            printer.decode_endpoint_equality(target).is_none(),
            "{surface}"
        );
        assert!(
            printer
                .format_bv_shared_endpoint_constant_conflict(ProofId(1), &[f.literal])
                .is_none(),
            "{surface}"
        );
    }
}

#[test]
fn consistent_endpoint_surfaces_keep_the_direct_lowering() {
    let f = fixture();
    for shared_surface in ["t", "(bvadd t #x00)"] {
        let overrides: DetHashMap<_, _> = [
            (f.shared, shared_surface.to_string()),
            // Literal spelling and whitespace do not change parsed identity.
            (f.left, format!("(=  {shared_surface}  (_ bv5 8))")),
            (f.right, format!("(= #x06 {shared_surface})")),
        ]
        .into_iter()
        .collect();
        let printer = AlethePrinter::new_with_overrides(&f.terms, Some(&overrides));
        let text = printer
            .format_bv_shared_endpoint_constant_conflict(ProofId(1), &[f.literal])
            .expect("both printed equalities still have the same endpoint");
        assert!(text.contains("t1.sec.t"), "{text}");
        assert!(text.contains(":rule eq_transitive"), "{text}");
        assert!(text.contains(":rule evaluate"), "{text}");
        assert!(!text.contains(":rule hole") && !text.contains(":rule trust"));
    }
}

#[test]
fn theory_formatter_does_not_select_the_mismatched_endpoint_route() {
    let f = fixture();
    let step = ProofStep::TheoryLemma {
        theory: "bv".to_string(),
        clause: vec![f.literal],
        farkas: None,
        kind: ay_core::TheoryLemmaKind::BvBitBlast,
        lia: None,
    };
    let plain = AlethePrinter::new_with_overrides(&f.terms, None);
    let text = plain.format_step(&step, ProofId(1)).unwrap();
    assert!(
        text.contains("t1.sec.t"),
        "the positive dispatch must exercise this route"
    );

    let overrides = [(f.left, "(= (bvadd t #x00) #x05)".to_string())]
        .into_iter()
        .collect();
    let printer = AlethePrinter::new_with_overrides(&f.terms, Some(&overrides));
    if let Ok(text) = printer.format_step(&step, ProofId(1)) {
        // Other established lowerings may independently prove the clause.
        // This regression grants none of them authority merely for rendering.
        assert!(!text.contains("t1.sec."), "{text}");
    }
}

#[test]
fn endpoint_surface_check_does_not_admit_an_exhausted_rendering() {
    let f = fixture();
    let printer = AlethePrinter::new_with_overrides_and_budget(&f.terms, None, Some(1));
    assert!(printer
        .format_bv_shared_endpoint_constant_conflict(ProofId(1), &[f.literal])
        .is_none());
    assert!(printer.work_budget_exhausted());
}
