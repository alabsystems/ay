// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A congruence operand whose PRINTED argument order is not its INTERNAL one.
//!
//! `decode_surface_congruence` reads one argument list off the printed
//! application and one off the term DAG, then treats position `k` of each as
//! the same position. A whole-application surface override restores the
//! AUTHOR's spelling, and for an equality the term store order-normalizes,
//! the author's order need not be the stored one.
//!
//! MEASURED on `benchmarks/smt/QF_ABV/csplit_repro_100selects_unsat.smt2`,
//! whose `(assert (not (= (select arr2 idx) val1)))` interns as
//! `(= val1 (select arr2 idx))` once ROW1 identifies the two. Step `t6`
//! printed `(= (select arr2 idx) val1)` over internal args
//! `[val1, (select arr2 idx)]`, so the printed `(select arr2 idx)` was paired
//! with the internal `val1`: the position looked internally REFLEXIVE between
//! two unrelated spellings, the narrow multiplication repair correctly
//! declined it, and — the exporter correctly refusing a `:rule trust`
//! fallback (#8821) — the query published `unsat` with NO Alethe document at
//! all, while its own premise already proved exactly `(= (select arr2 idx)
//! val1)`.
//!
//! The fixture below is that step, with the ROW1 chain that proves its
//! premise kept as real derivation steps so no `assume` spells the bridged
//! equality (the authored-assume repair must not be what rescues it).
//!
//! The permuted reading is a SECOND reading, never a replacement: a printed
//! operand list that is a permutation of the rendered internal one is
//! genuinely ambiguous, because equality substitution can re-spell one operand
//! AS the other without permuting anything. `decode_surface_congruence`
//! therefore offers the stored order first, and ay-dpll's
//! `implied_equality_inside_a_congruence` — `(= _4 |k#s1_0|)` printed as the
//! authored `(= |k#s1_0| _4)`, discharged by the authored-implication bridge
//! under the STORED reading — is the row that pins that order. The second
//! test below pins the same thing from this side: with nothing re-spelling the
//! operands there is only one reading and the step renders as it always did.

use crate::{try_export_alethe_with_problem_scope_and_overrides, AlethePrintError};
use ay_core::kani_compat::DetHashMap;
use ay_core::{AletheRule, ArraySort, Proof, Sort, Symbol, TermId, TermStore};

fn equality(terms: &mut TermStore, left: TermId, right: TermId) -> TermId {
    terms.mk_app(Symbol::named("="), [left, right], Sort::Bool)
}

struct OperandOrderFixture {
    terms: TermStore,
    proof: Proof,
    overrides: DetHashMap<TermId, String>,
    scope: Vec<TermId>,
}

/// `re_spelling` is the surface override recorded for the equality the
/// congruence rewrites. `None` leaves the stored order, where printed and
/// internal positions already correspond and nothing is realigned.
fn build(re_spelling: Option<&str>) -> OperandOrderFixture {
    let mut terms = TermStore::new();
    let array = Sort::Array(Box::new(ArraySort {
        index_sort: Sort::Int,
        element_sort: Sort::Int,
    }));
    let base = terms.mk_var("arr", array.clone());
    let aliased = terms.mk_var("arr2", array.clone());
    let index = terms.mk_var("idx", Sort::Int);
    let value = terms.mk_var("val1", Sort::Int);
    let stored = terms.mk_app(Symbol::named("store"), [base, index, value], array);
    let read_alias = terms.mk_app(Symbol::named("select"), [aliased, index], Sort::Int);
    let read_store = terms.mk_app(Symbol::named("select"), [stored, index], Sort::Int);

    // The equality the congruence rewrites, in the order the term store holds
    // it: value first, the read second.
    let rewritten = equality(&mut terms, value, read_alias);
    let folded = equality(&mut terms, value, value);
    let conclusion = equality(&mut terms, rewritten, folded);

    // The ROW1 chain that PROVES `(= (select arr2 idx) val1)`. Neither leaf
    // carries that equality itself, so the printer's authored-assume bridge
    // has nothing to find and the realignment under test is the only thing
    // that can render the step.
    let alias_definition = equality(&mut terms, aliased, stored);
    let alias_congruence = equality(&mut terms, read_alias, read_store);
    let row1 = equality(&mut terms, read_store, value);
    let bridged = equality(&mut terms, read_alias, value);

    let mut proof = Proof::new();
    let definition = proof.add_assume(alias_definition, None);
    let row = proof.add_assume(row1, None);
    let congruence = proof.add_rule_step(
        AletheRule::Cong,
        vec![alias_congruence],
        vec![definition],
        Vec::new(),
    );
    let premise = proof.add_rule_step(
        AletheRule::Trans,
        vec![bridged],
        vec![congruence, row],
        Vec::new(),
    );
    proof.add_rule_step(
        AletheRule::Cong,
        vec![conclusion],
        vec![premise],
        Vec::new(),
    );

    let mut overrides = DetHashMap::default();
    if let Some(re_spelling) = re_spelling {
        overrides.insert(rewritten, re_spelling.to_string());
    }

    OperandOrderFixture {
        terms,
        proof,
        overrides,
        scope: vec![alias_definition, row1],
    }
}

fn export(fixture: &OperandOrderFixture) -> Result<String, AlethePrintError> {
    try_export_alethe_with_problem_scope_and_overrides(
        &fixture.proof,
        &fixture.terms,
        &fixture.scope,
        Some(&fixture.overrides),
    )
}

/// The regression. The printed operands are the stored ones commuted, and the
/// document's own `t3` proves exactly the printed position, so the step must
/// render — citing that premise — instead of refusing the whole export.
#[test]
fn a_commuted_printed_operand_is_paired_with_the_argument_that_prints_as_it() {
    let fixture = build(Some("(= (select arr2 idx) val1)"));
    let output = export(&fixture).expect(
        "the printed position is proved by the document's own premise and must render, not decline",
    );
    assert!(
        output.contains(
            "(step t4 (cl (= (= (select arr2 idx) val1) (= val1 val1))) :rule cong :premises (t3))"
        ),
        "{output}"
    );
    // Nothing was bought with an unchecked step.
    assert!(!output.contains(":rule hole"), "{output}");
    assert!(!output.contains(":rule trust"), "{output}");
}

/// CONTROL. With no override the printed order IS the stored order, so no
/// realignment happens and the same step renders exactly as it always did.
#[test]
fn the_stored_order_is_untouched_when_nothing_re_spells_the_operands() {
    let fixture = build(None);
    let output = export(&fixture).expect("an un-overridden congruence renders as it always did");
    assert!(
        output.contains(
            "(step t4 (cl (= (= val1 (select arr2 idx)) (= val1 val1))) :rule cong :premises (t3))"
        ),
        "{output}"
    );
}

/// NEGATIVE CONTROL: realignment is an EXACT assignment, never a guess. An
/// override that re-spells an operand as text no internal argument renders as
/// leaves the stored order in place, and the loud refusal is unchanged — the
/// printer must not reach for the nearest argument to make a step render.
#[test]
fn an_operand_no_internal_argument_renders_as_keeps_the_refusal() {
    let fixture = build(Some("(= (select arr9 idx) val1)"));
    let error = export(&fixture)
        .expect_err("no internal argument renders as `(select arr9 idx)`, so nothing is realigned");
    let reason = format!("{error}");
    assert!(
        reason.contains("position-preserving congruence"),
        "the loud refusal must survive: {reason}"
    );
    assert!(
        reason.contains(r#"left="(select arr9 idx)""#),
        "the refusal must name the spelling it could not place: {reason}"
    );
}
