// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! [`dt_project_lowering_supported`], the known-wire-gap screen's view of the
//! `dt_project` lowering, against what the printer actually prints; the
//! AY-internal identity decline; and the anchor-binder decline the screen
//! cannot see.
//!
//! REGRESSION (measured 2026-10-02 on the dt_project commit): with
//! `(set-option :check-proofs-strict true)` the Clean dialect withheld the
//! UNSAT of `(assert (not (= (fst (mk a b)) a)))` as `unknown (incomplete
//! proof-trusted)`, "its Alethe rendering has a known wire gap no external
//! checker accepts", though the document it renders is hole-free and Clean
//! passes it: the screen read the kind's wire rule, `hole`. And two datatypes
//! that share the field name `f1` printed `dt_project` over the frontend's
//! `__ay_overload_1`, a name the problem never declares.

use super::super::dialect::{capture_alethe_dialect_report, with_alethe_dialect, AletheDialect};
use super::super::AlethePrinter;
use super::dt_project_lowering_supported;
use ay_core::kani_compat::DetHashMap;
use ay_core::{Proof, ProofId, ProofStep, Sort, Symbol, TermId, TermStore, TheoryLemmaKind};

/// `mk(sel_0, sel_1)` over the free `a`, `b`, registered as the frontend
/// does, and `(= (selector (mk a b)) value)` or reversed.
struct Fixture {
    terms: TermStore,
    a: TermId,
    b: TermId,
    built: TermId,
}

impl Fixture {
    fn new(constructor: &str, selectors: [&str; 2]) -> Self {
        let mut terms = TermStore::new();
        terms.register_constructor_fields(
            constructor,
            selectors.iter().map(ToString::to_string).collect(),
        );
        let a = terms.mk_var("a", Sort::Int);
        let b = terms.mk_var("b", Sort::Int);
        let built = terms.mk_app(
            Symbol::named(constructor),
            [a, b],
            Sort::Uninterpreted("Pair".to_string()),
        );
        Self { terms, a, b, built }
    }

    fn selection(&mut self, selector: &str) -> TermId {
        self.terms
            .mk_app(Symbol::named(selector), [self.built], Sort::Int)
    }

    fn equal(&mut self, left: TermId, right: TermId) -> TermId {
        self.terms
            .mk_app(Symbol::named("="), [left, right], Sort::Bool)
    }
}

/// Whether the printer, in `dialect` and under `overrides`, prints the lemma
/// `clause` as `dt_project`.
fn printer_prints_dt_project(
    terms: &TermStore,
    clause: &[TermId],
    overrides: Option<&DetHashMap<TermId, String>>,
    dialect: AletheDialect,
) -> bool {
    let step = ProofStep::TheoryLemma {
        theory: "datatype".to_string(),
        clause: clause.to_vec(),
        farkas: None,
        kind: TheoryLemmaKind::DatatypeSelectorProject,
        lia: None,
    };
    let (text, _) = capture_alethe_dialect_report(|| {
        with_alethe_dialect(dialect, || {
            AlethePrinter::new_with_overrides_and_budget(terms, overrides, None)
                .format_step(&step, ProofId(1))
                .expect("a selector-projection lemma renders")
        })
    });
    let printed = text.contains(":rule dt_project)");
    assert_eq!(
        printed,
        !text.contains(":rule hole)"),
        "a projection lemma prints dt_project or the hole: {text}"
    );
    printed
}

/// The screen and the printer agree, case by case, in both dialects.
#[test]
fn the_screen_predicts_the_printer() {
    let mut fixture = Fixture::new("mk", ["fst", "snd"]);
    let (a, b) = (fixture.a, fixture.b);
    let fst = fixture.selection("fst");
    let forward = fixture.equal(fst, a);
    let reversed = fixture.equal(a, fst);
    let wrong_field = fixture.equal(fst, b);
    // An authored spelling of the selection whose `t_0` is not the printed
    // right side: the IR projection holds, the printed text does not.
    let respelled: DetHashMap<TermId, String> =
        std::iter::once((fst, "(fst (mk c b))".to_string())).collect();
    // An authored spelling the projection survives.
    let same: DetHashMap<TermId, String> =
        std::iter::once((fst, "(fst (mk a b))".to_string())).collect();
    let cases: [(&str, Vec<TermId>, Option<&DetHashMap<TermId, String>>, bool); 6] = [
        ("selector first", vec![forward], None, true),
        ("value first", vec![reversed], None, true),
        ("the wrong field", vec![wrong_field], None, false),
        ("two literals", vec![forward, wrong_field], None, false),
        (
            "an override that respells t_0",
            vec![forward],
            Some(&respelled),
            false,
        ),
        ("an identity override", vec![forward], Some(&same), true),
    ];
    for (label, clause, overrides, clean) in cases {
        for dialect in [AletheDialect::Clean, AletheDialect::PinnedCarcara] {
            let expected = clean && dialect == AletheDialect::Clean;
            let screened =
                dt_project_lowering_supported(dialect, &fixture.terms, &clause, overrides);
            assert_eq!(screened, expected, "{label} in {dialect:?}: the screen");
            assert_eq!(
                printer_prints_dt_project(&fixture.terms, &clause, overrides, dialect),
                expected,
                "{label} in {dialect:?}: the printer"
            );
        }
    }
}

/// The frontend's `__ay_overload_N` identity (a selector two datatypes share)
/// is a name no problem declares: the step keeps the hole, whether it prints
/// as a simple symbol or quoted (`|__ay_overload 1|`).
#[test]
fn an_internal_identity_keeps_the_hole() {
    for (constructor, selector) in [
        ("mkq", "__ay_overload_1"),
        ("__ay_overload_0", "f1"),
        ("mkq", "__ay_overload 1"),
    ] {
        let mut fixture = Fixture::new(constructor, [selector, "f2"]);
        let a = fixture.a;
        let selection = fixture.selection(selector);
        let literal = fixture.equal(selection, a);
        assert!(
            !printer_prints_dt_project(&fixture.terms, &[literal], None, AletheDialect::Clean),
            "{constructor}/{selector}"
        );
        assert!(
            !dt_project_lowering_supported(AletheDialect::Clean, &fixture.terms, &[literal], None),
            "{constructor}/{selector}"
        );
    }
    // A user name that merely contains the prefix later is still a name.
    let mut fixture = Fixture::new("mk", ["my__ay_field", "f2"]);
    let a = fixture.a;
    let selection = fixture.selection("my__ay_field");
    let literal = fixture.equal(selection, a);
    assert!(printer_prints_dt_project(
        &fixture.terms,
        &[literal],
        None,
        AletheDialect::Clean
    ));
}

/// The document `(assume t0 (not (= (fst (mk a b)) a)))`, the lemma `t1`,
/// the empty resolvent `t2`, and, when `binder` names one, an IR anchor over
/// `t2` that binds it, exported whole in the Clean dialect.
fn clean_document_with_anchor(binder: Option<&str>) -> String {
    let mut fixture = Fixture::new("mk", ["fst", "snd"]);
    let a = fixture.a;
    let fst = fixture.selection("fst");
    let literal = fixture.equal(fst, a);
    let negated = fixture.terms.mk_not_raw(literal);
    let mut proof = Proof::default();
    let assumed = proof.add_assume(negated, None);
    let projected = proof.add_theory_lemma_with_kind(
        "datatype",
        vec![literal],
        TheoryLemmaKind::DatatypeSelectorProject,
    );
    let empty = proof.add_resolution(vec![], literal, assumed, projected);
    if let Some(binder) = binder {
        proof.steps.push(ProofStep::Anchor {
            end_step: empty,
            variables: vec![(binder.to_string(), Sort::Int)],
        });
    }
    // The screen sees no proof, so it cannot see the anchor: it stays
    // optimistic, which costs only a disclosed hole.
    assert!(dt_project_lowering_supported(
        AletheDialect::Clean,
        &fixture.terms,
        &[literal],
        None
    ));
    with_alethe_dialect(AletheDialect::Clean, || {
        crate::try_export_alethe_with_problem_scope_overrides_and_budget(
            &proof,
            &fixture.terms,
            &[negated],
            None,
            None,
        )
        .expect("the refutation exports")
    })
}

/// Clean refuses `dt_project` under an anchor that binds `S` or `C`, so a
/// proof whose IR anchor binds the selector or the constructor keeps the hole
/// for the lemma. The binders come from `prepare_proof` on the whole proof,
/// through `format_dt_project`, not from a closure handed to
/// `printed_dt_project`: with that method's `bound` closure replaced by
/// `|_name| false` (review round 3's mutant M8) both binder cases print
/// `dt_project`. An anchor binding another name changes nothing.
#[test]
fn an_anchor_binding_the_selector_or_the_constructor_keeps_the_hole() {
    let lemma = "(step t1 (cl (= (fst (mk a b)) a)) :rule";
    let mut wrong = Vec::new();
    for (binder, projected) in [
        (None, true),
        (Some("c"), true),
        (Some("fst"), false),
        (Some("mk"), false),
    ] {
        let document = clean_document_with_anchor(binder);
        if let Some(binder) = binder {
            assert!(
                document.contains(&format!("(anchor :step t2 :args (({binder} Int)))")),
                "{binder}: the anchor is printed\n{document}"
            );
        }
        let rule = if projected { "dt_project" } else { "hole" };
        let expected = format!("{lemma} {rule})");
        if !document.lines().any(|line| line == expected)
            || document.contains("dt_project") != projected
        {
            wrong.push(format!("{binder:?}: expected {expected}\n{document}"));
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}
