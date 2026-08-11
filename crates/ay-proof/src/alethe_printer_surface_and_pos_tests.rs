// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::{
    check_proof_strict, try_export_alethe_with_problem_scope_and_overrides, AlethePrintError,
    AlethePrinter,
};
use ay_core::kani_compat::DetHashMap;
use ay_core::{AletheRule, Proof, ProofId, ProofStep, Sort, Symbol, TermId, TermStore};

fn raw_and(terms: &mut TermStore, children: impl IntoIterator<Item = TermId>) -> TermId {
    let children: Vec<TermId> = children.into_iter().collect();
    terms.mk_app(Symbol::named("and"), children, Sort::Bool)
}

fn and_pos_step(position: u32, gate: TermId, selected: TermId, source: TermId) -> ProofStep {
    ProofStep::Step {
        rule: AletheRule::AndPos(position),
        clause: vec![gate, selected],
        premises: Vec::new(),
        args: vec![source],
    }
}

#[test]
fn flat_surface_and_pos_keeps_aligned_default_bytes() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("flat_and_default_a", Sort::Bool);
    let b = terms.mk_var("flat_and_default_b", Sort::Bool);
    let source = raw_and(&mut terms, [a, b]);
    let gate = terms.mk_not_raw(source);
    let printer = AlethePrinter::new(&terms);

    let printed = printer
        .format_step(&and_pos_step(0, gate, a, source), ProofId(7))
        .expect("aligned projection");
    assert_eq!(
        printed,
        "(step t7 (cl (not (and flat_and_default_a flat_and_default_b)) flat_and_default_a) :rule and_pos :args (0))"
    );
}

#[test]
fn flat_surface_and_pos_repairs_reordered_index_and_clause_order() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("flat_and_reorder_a", Sort::Bool);
    let b = terms.mk_var("flat_and_reorder_b", Sort::Bool);
    let c = terms.mk_var("flat_and_reorder_c", Sort::Bool);
    let source = raw_and(&mut terms, [a, b, c]);
    let gate = terms.mk_not_raw(source);
    let mut overrides = DetHashMap::default();
    overrides.insert(
        source,
        "(and flat_and_reorder_c flat_and_reorder_a flat_and_reorder_b)".to_string(),
    );
    let printer = AlethePrinter::new_with_overrides(&terms, Some(&overrides));
    let reversed = ProofStep::Step {
        rule: AletheRule::AndPos(0),
        clause: vec![a, gate],
        premises: Vec::new(),
        args: vec![source],
    };

    let printed = printer
        .format_step(&reversed, ProofId(3))
        .expect("surface index repair");
    assert_eq!(
        printed,
        "(step t3 (cl (not (and flat_and_reorder_c flat_and_reorder_a flat_and_reorder_b)) flat_and_reorder_a) :rule and_pos :args (1))"
    );
}

#[test]
fn flat_surface_and_pos_uses_first_identical_surface_operand() {
    let mut terms = TermStore::new();
    let f = terms.mk_bool(false);
    let a = terms.mk_var("flat_and_duplicate_a", Sort::Bool);
    let source = raw_and(&mut terms, [a, f, f]);
    let gate = terms.mk_not_raw(source);
    let mut overrides = DetHashMap::default();
    overrides.insert(source, "(and false flat_and_duplicate_a false)".to_string());
    let printer = AlethePrinter::new_with_overrides(&terms, Some(&overrides));

    let printed = printer
        .format_step(&and_pos_step(2, gate, f, source), ProofId(2))
        .expect("either identical false occurrence is a valid projection");
    assert_eq!(
        printed,
        "(step t2 (cl (not (and false flat_and_duplicate_a false)) false) :rule and_pos :args (0))"
    );
}

#[test]
fn flat_surface_and_pos_handles_strings_and_escaped_symbols_in_real_export() {
    let mut terms = TermStore::new();
    let s = terms.mk_var("flat_and_string_s", Sort::String);
    let value = terms.mk_string("a)\"b".to_string());
    let equality = terms.mk_app(Symbol::named("="), [s, value], Sort::Bool);
    let exotic = terms.mk_var("a|b\\c", Sort::Bool);
    let p = terms.mk_var("flat_and_string_p", Sort::Bool);
    let source = raw_and(&mut terms, [exotic, equality, p]);
    let gate = terms.mk_not_raw(source);
    let mut overrides = DetHashMap::default();
    overrides.insert(
        source,
        r#"(and(= flat_and_string_s "a)""b")|a\|b\\c| flat_and_string_p)"#.to_string(),
    );
    let mut proof = Proof::new();
    proof.add_rule_step(
        AletheRule::AndPos(0),
        vec![gate, exotic],
        Vec::new(),
        vec![source],
    );

    let output = try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &[source],
        Some(&overrides),
    )
    .expect("shared scanner must preserve exotic surface operands");
    assert!(
        output.contains(
            r#"(step t0 (cl (not (and(= flat_and_string_s "a)""b")|a\|b\\c| flat_and_string_p)) |a\|b\\c|) :rule and_pos :args (1))"#
        ),
        "{output}"
    );
}

#[test]
fn flat_surface_and_pos_exports_delimiter_adjacent_lists() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("flat_and_adjacent_a", Sort::Bool);
    let b = terms.mk_var("flat_and_adjacent_b", Sort::Bool);
    let not_a = terms.mk_not_raw(a);
    let not_b = terms.mk_not_raw(b);
    let source = raw_and(&mut terms, [not_a, not_b]);
    let gate = terms.mk_not_raw(source);
    let mut overrides = DetHashMap::default();
    overrides.insert(
        source,
        "(and(not flat_and_adjacent_a)(not flat_and_adjacent_b))".to_string(),
    );
    let mut proof = Proof::new();
    proof.add_rule_step(
        AletheRule::AndPos(1),
        vec![gate, not_b],
        Vec::new(),
        vec![source],
    );

    let output = try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &[source],
        Some(&overrides),
    )
    .expect("legal delimiter adjacency must survive real step export");
    assert!(
        output.contains(
            "(step t0 (cl (not (and(not flat_and_adjacent_a)(not flat_and_adjacent_b))) (not flat_and_adjacent_b)) :rule and_pos :args (1))"
        ),
        "{output}"
    );
}

#[test]
fn flat_surface_and_pos_rejects_no_match_and_malformed_contracts() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("flat_and_bad_a", Sort::Bool);
    let b = terms.mk_var("flat_and_bad_b", Sort::Bool);
    let _c = terms.mk_var("flat_and_bad_c", Sort::Bool);
    let source = raw_and(&mut terms, [a, b]);
    let gate = terms.mk_not_raw(source);
    let mut overrides = DetHashMap::default();
    overrides.insert(source, "(and flat_and_bad_b flat_and_bad_c)".to_string());
    let printer = AlethePrinter::new_with_overrides(&terms, Some(&overrides));
    let error = printer
        .format_step(&and_pos_step(0, gate, a, source), ProofId(4))
        .expect_err("missing selected surface child must fail closed");
    assert!(
        matches!(error, AlethePrintError::InvalidSurfaceStep { ref reason, .. }
            if reason.contains("absent from its effective source")),
        "{error}"
    );

    let malformed = ProofStep::Step {
        rule: AletheRule::AndPos(0),
        clause: vec![gate, a],
        premises: vec![ProofId(0)],
        args: vec![source],
    };
    let error = AlethePrinter::new(&terms)
        .format_step(&malformed, ProofId(5))
        .expect_err("and_pos premise must not reach default emission");
    assert!(
        matches!(error, AlethePrintError::InvalidSurfaceStep { ref reason, .. }
            if reason.contains("requires no premises")),
        "{error}"
    );
}

#[test]
fn not_implies_bridge_still_precedes_flat_and_pos_gate() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("flat_and_implies_a", Sort::Bool);
    let b = terms.mk_var("flat_and_implies_b", Sort::Bool);
    let not_b = terms.mk_not_raw(b);
    let source = raw_and(&mut terms, [a, not_b]);
    let gate = terms.mk_not_raw(source);
    let mut overrides = DetHashMap::default();
    overrides.insert(
        source,
        "(not (=> flat_and_implies_a flat_and_implies_b))".to_string(),
    );
    let printer = AlethePrinter::new_with_overrides(&terms, Some(&overrides));

    let printed = printer
        .format_step(&and_pos_step(0, gate, a, source), ProofId(6))
        .expect("negated implication uses its dedicated derivation");
    assert!(printed.contains("(step t6.imp"), "{printed}");
    assert!(printed.contains(":rule implies_neg1"), "{printed}");
    assert!(printed.contains(":rule not_simplify"), "{printed}");
}

#[test]
fn flat_surface_and_pos_preserves_empty_and_trailing_internal_args() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("flat_and_args_a", Sort::Bool);
    let b = terms.mk_var("flat_and_args_b", Sort::Bool);
    let source = raw_and(&mut terms, [a, b]);
    let gate = terms.mk_not_raw(source);
    let not_b = terms.mk_not_raw(b);
    let printer = AlethePrinter::new(&terms);

    for args in [Vec::new(), vec![source, a, b], vec![a, source]] {
        let step = ProofStep::Step {
            rule: AletheRule::AndPos(1),
            clause: vec![gate, b],
            premises: Vec::new(),
            args,
        };
        let output = printer
            .format_step(&step, ProofId(8))
            .expect("native source inference/trailing args remain compatible");
        assert_eq!(
            output,
            "(step t8 (cl (not (and flat_and_args_a flat_and_args_b)) flat_and_args_b) :rule and_pos :args (1))"
        );
        let mut proof = Proof::new();
        let projection = proof.add_step(step);
        let source_assume = proof.add_assume(source, None);
        let selected = proof.add_resolution(vec![b], source, source_assume, projection);
        let not_b_assume = proof.add_assume(not_b, None);
        proof.add_resolution(Vec::new(), b, selected, not_b_assume);
        check_proof_strict(&proof, &terms).expect("the mirrored native source fallback is valid");
    }
}

#[test]
fn flat_surface_and_pos_over_64_is_linear_and_repeated_budget_is_typed() {
    let mut terms = TermStore::new();
    let children: Vec<TermId> = (0..96)
        .map(|index| terms.mk_var(format!("flat_and_wide_{index}"), Sort::Bool))
        .collect();
    let source = raw_and(&mut terms, children.iter().copied());
    let gate = terms.mk_not_raw(source);
    let step = and_pos_step(95, gate, children[95], source);

    let probe = AlethePrinter::new(&terms);
    let first = probe
        .format_step(&step, ProofId(0))
        .expect("explicit proofs are not limited by DPLL's copied-role arity cap");
    assert!(first.ends_with(":rule and_pos :args (95))"), "{first}");
    let one_step_work = probe.work_used();
    assert!(one_step_work > 0);
    assert!(
        one_step_work <= (first.len() as u64).saturating_mul(24),
        "linear renderer charged {one_step_work} work for {} output bytes",
        first.len()
    );

    let bounded = AlethePrinter::new_with_overrides_and_budget(&terms, None, Some(one_step_work));
    bounded
        .format_step(&step, ProofId(0))
        .expect("one exact linear pass fits its measured budget");
    let error = bounded
        .format_step(&step, ProofId(1))
        .expect_err("the repeated scan must debit the shared emission budget");
    assert!(
        matches!(
            error,
            AlethePrintError::EmissionBudgetExhausted {
                steps_rendered: 1,
                ..
            }
        ),
        "{error}"
    );
}

// ---------------------------------------------------------------------------
// Non-vacuity of the ROW1 / eq_congruent SURFACE validators.
//
// A certified step is printed through a table that may re-spell any `TermId`.
// These pin that the validators reject a printed step whose operand spelling
// denotes something OTHER than the term the strict checker certified, so no
// later change can quietly turn the guard into a rubber stamp. They are
// independent of how a producer arranges for such a divergence not to arise.
// ---------------------------------------------------------------------------

fn bv8(terms: &mut TermStore, value: u32) -> TermId {
    terms.mk_bitvec(num_bigint::BigInt::from(value), 8)
}

/// The certified unit ROW1 lemma `(= (select (store mem p V) p) V)`, returning
/// its `store` subterm (the override handle these tests re-spell) too.
fn row1_fixture(terms: &mut TermStore, value: u32) -> (TermId, ProofStep) {
    let index_sort = Sort::bitvec(8);
    let element_sort = Sort::bitvec(8);
    let array_sort = Sort::array(index_sort.clone(), element_sort.clone());
    let mem = terms.mk_var("row1_mem", array_sort.clone());
    let p = terms.mk_var("row1_p", index_sort);
    let stored = bv8(terms, value);
    // RAW applications: `mk_store`/`mk_select` apply the ROW1 identity
    // themselves, which is precisely the step being certified here.
    let store = terms.mk_app(Symbol::named("store"), vec![mem, p, stored], array_sort);
    let select = terms.mk_app(Symbol::named("select"), vec![store, p], element_sort);
    let row = terms.mk_app(Symbol::named("="), vec![select, stored], Sort::Bool);
    let step = ProofStep::TheoryLemma {
        theory: "array".to_string(),
        clause: vec![row],
        farkas: None,
        kind: ay_core::TheoryLemmaKind::ArraySelectStore { index_eq: true },
        lia: None,
    };
    (store, step)
}

#[test]
fn row1_without_surface_spellings_prints_the_certified_terms() {
    let mut terms = TermStore::new();
    let (_, step) = row1_fixture(&mut terms, 0x10);
    let printer = AlethePrinter::new(&terms);

    assert_eq!(
        printer
            .format_step(&step, ProofId(1))
            .expect("the identity rendering of a certified ROW1 is checkable"),
        "(step t1 (cl (= (select (store row1_mem row1_p #b00010000) row1_p) #b00010000)) \
         :rule arrays_idx)"
    );
}

#[test]
fn row1_rejects_a_store_value_surface_denoting_a_different_constant() {
    let mut terms = TermStore::new();
    let (store, step) = row1_fixture(&mut terms, 0x10);
    let mut overrides = DetHashMap::default();
    // Same shape, same array, same index — a DIFFERENT written value.
    overrides.insert(store, "(store row1_mem row1_p #b11111111)".to_string());
    let printer = AlethePrinter::new_with_overrides(&terms, Some(&overrides));

    let error = printer
        .format_step(&step, ProofId(1))
        .expect_err("a store value that is not the certified one must be refused");
    assert!(
        matches!(error, AlethePrintError::InvalidArrayStep { .. }),
        "{error}"
    );
}

#[test]
fn row1_rejects_a_store_index_surface_denoting_a_different_term() {
    let mut terms = TermStore::new();
    let (store, step) = row1_fixture(&mut terms, 0x10);
    let mut overrides = DetHashMap::default();
    overrides.insert(store, "(store row1_mem row1_other #b00010000)".to_string());
    let printer = AlethePrinter::new_with_overrides(&terms, Some(&overrides));

    let error = printer
        .format_step(&step, ProofId(1))
        .expect_err("a write address that is not the certified one must be refused");
    assert!(
        matches!(error, AlethePrintError::InvalidArrayStep { .. }),
        "{error}"
    );
}

#[test]
fn row1_rejects_a_base_array_surface_denoting_a_different_array() {
    let mut terms = TermStore::new();
    let (store, step) = row1_fixture(&mut terms, 0x10);
    let mut overrides = DetHashMap::default();
    overrides.insert(
        store,
        "(store row1_other_mem row1_p #b00010000)".to_string(),
    );
    let printer = AlethePrinter::new_with_overrides(&terms, Some(&overrides));

    let error = printer
        .format_step(&step, ProofId(1))
        .expect_err("a base array that is not the certified one must be refused");
    assert!(
        matches!(error, AlethePrintError::InvalidArrayStep { .. }),
        "{error}"
    );
}

/// `(cl (not (= a b)) (= (f a) (f b)))` re-spelled so the congruent
/// application is printed at a THIRD term no hypothesis mentions.
#[test]
fn eq_congruent_rejects_a_surface_argument_denoting_a_different_term() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("cong_a", Sort::bitvec(8));
    let b = terms.mk_var("cong_b", Sort::bitvec(8));
    let fa = terms.mk_app(Symbol::named("cong_f"), vec![a], Sort::bitvec(8));
    let fb = terms.mk_app(Symbol::named("cong_f"), vec![b], Sort::bitvec(8));
    let equality = terms.mk_app(Symbol::named("="), vec![a, b], Sort::Bool);
    let negated = terms.mk_not_raw(equality);
    let conclusion = terms.mk_app(Symbol::named("="), vec![fa, fb], Sort::Bool);
    let step = ProofStep::Step {
        rule: AletheRule::EqCongruent,
        clause: vec![negated, conclusion],
        premises: Vec::new(),
        args: Vec::new(),
    };

    let plain = AlethePrinter::new(&terms);
    assert_eq!(
        plain
            .format_step(&step, ProofId(2))
            .expect("the identity rendering of a certified congruence is checkable"),
        "(step t2 (cl (not (= cong_a cong_b)) (= (cong_f cong_a) (cong_f cong_b))) \
         :rule eq_congruent)"
    );

    // The hypothesis still names `cong_a`, but the left application is now
    // printed at a term the clause never equates. The AC bridge is the only
    // repair the printer has, and it must not fire on an argument pair it
    // cannot prove equal.
    let mut overrides = DetHashMap::default();
    overrides.insert(fa, "(cong_f cong_elsewhere)".to_string());
    let printer = AlethePrinter::new_with_overrides(&terms, Some(&overrides));
    let error = printer
        .format_step(&step, ProofId(2))
        .expect_err("a congruence argument that is not the certified one must be refused");
    assert!(
        matches!(error, AlethePrintError::InvalidCongruenceStep { .. }),
        "{error}"
    );
}
