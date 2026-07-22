// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for string lemma clause creation and length axiom collection.

use ay_core::term::Symbol;
use ay_core::term::TermData;
use ay_core::{Sort, StringLemma, StringLemmaKind, TheoryLit};
use num_bigint::BigInt;

use super::super::super::Executor;
use super::super::skolem_cache::ExecutorSkolemCache;
use super::*;

#[test]
fn build_reason_guard_true_reason_negates_term() {
    let mut exec = Executor::new();
    let x = exec.ctx.terms.mk_fresh_var("x", Sort::String);
    let empty = exec.ctx.terms.mk_string(String::new());
    let x_empty = exec.ctx.terms.mk_eq(x, empty);

    let clause = build_reason_guard(&mut exec.ctx.terms, &[TheoryLit::new(x_empty, true)], 1);

    assert_eq!(clause, vec![exec.ctx.terms.mk_not(x_empty)]);
}

#[test]
fn build_reason_guard_false_reason_keeps_term() {
    let mut exec = Executor::new();
    let x = exec.ctx.terms.mk_fresh_var("x", Sort::String);
    let empty = exec.ctx.terms.mk_string(String::new());
    let x_empty = exec.ctx.terms.mk_eq(x, empty);

    let clause = build_reason_guard(&mut exec.ctx.terms, &[TheoryLit::new(x_empty, false)], 1);

    assert_eq!(clause, vec![x_empty]);
}

#[test]
fn emit_guard_empty_splits_emits_tautology_for_positive_eq_empty() {
    let mut exec = Executor::new();
    let x = exec.ctx.terms.mk_fresh_var("x", Sort::String);
    let empty = exec.ctx.terms.mk_string(String::new());
    let x_empty = exec.ctx.terms.mk_eq(x, empty);

    let splits = emit_guard_empty_splits(&mut exec.ctx.terms, &[TheoryLit::new(x_empty, true)]);

    assert_eq!(splits, vec![vec![x_empty, exec.ctx.terms.mk_not(x_empty)]]);
}

#[test]
fn emit_guard_empty_splits_ignores_negative_and_non_empty_guards() {
    let mut exec = Executor::new();
    let x = exec.ctx.terms.mk_fresh_var("x", Sort::String);
    let empty = exec.ctx.terms.mk_string(String::new());
    let abc = exec.ctx.terms.mk_string("abc".to_string());
    let x_empty = exec.ctx.terms.mk_eq(x, empty);
    let x_abc = exec.ctx.terms.mk_eq(x, abc);

    let splits = emit_guard_empty_splits(
        &mut exec.ctx.terms,
        &[TheoryLit::new(x_empty, false), TheoryLit::new(x_abc, true)],
    );

    assert!(
        splits.is_empty(),
        "non-positive or non-empty guards must be ignored"
    );
}

#[test]
fn emit_skolem_len_bridge_emits_len_ge_zero() {
    let mut exec = Executor::new();
    let k = exec.ctx.terms.mk_fresh_var("k", Sort::String);
    let len_k = exec
        .ctx
        .terms
        .mk_app(Symbol::named("str.len"), vec![k], Sort::Int);
    let zero = exec.ctx.terms.mk_int(BigInt::from(0));
    let empty = exec.ctx.terms.mk_string(String::new());
    let len_eq_zero = exec.ctx.terms.mk_eq(len_k, zero);
    let k_empty = exec.ctx.terms.mk_eq(k, empty);

    let clauses = exec.emit_skolem_len_bridge(k);

    assert_eq!(clauses.len(), 3, "bridge must emit three clauses");
    assert_eq!(clauses[0], vec![exec.ctx.terms.mk_ge(len_k, zero)]);
    assert_eq!(
        clauses[1],
        vec![exec.ctx.terms.mk_not(len_eq_zero), k_empty]
    );
    assert_eq!(
        clauses[2],
        vec![exec.ctx.terms.mk_not(k_empty), len_eq_zero]
    );
}

#[test]
fn lower_dynamic_axiom_implication_becomes_binary_clause() {
    let mut exec = Executor::new();
    let x = exec.ctx.terms.mk_fresh_var("x", Sort::String);
    let y = exec.ctx.terms.mk_fresh_var("y", Sort::String);
    let empty = exec.ctx.terms.mk_string(String::new());
    let x_empty = exec.ctx.terms.mk_eq(x, empty);
    let y_empty = exec.ctx.terms.mk_eq(y, empty);
    let implication = exec.ctx.terms.mk_implies(x_empty, y_empty);

    let clauses = exec.lower_dynamic_axiom_to_clauses(implication);

    assert_eq!(
        clauses.len(),
        1,
        "implication should lower to one CNF clause"
    );
    assert_eq!(clauses[0].len(), 2, "implication clause must be binary");
    assert!(
        clauses[0].contains(&exec.ctx.terms.mk_not(x_empty)),
        "clause must contain negated antecedent"
    );
    assert!(
        clauses[0].contains(&y_empty),
        "clause must contain consequent"
    );
}

#[test]
fn lower_dynamic_axiom_conjunction_becomes_unit_clauses() {
    let mut exec = Executor::new();
    let x = exec.ctx.terms.mk_fresh_var("x", Sort::String);
    let y = exec.ctx.terms.mk_fresh_var("y", Sort::String);
    let empty = exec.ctx.terms.mk_string(String::new());
    let x_empty = exec.ctx.terms.mk_eq(x, empty);
    let y_empty = exec.ctx.terms.mk_eq(y, empty);
    let conjunction = exec.ctx.terms.mk_and(vec![x_empty, y_empty]);

    let clauses = exec.lower_dynamic_axiom_to_clauses(conjunction);

    assert_eq!(clauses, vec![vec![x_empty], vec![y_empty]]);
}

#[test]
fn lower_dynamic_axiom_atom_stays_unit_clause() {
    let mut exec = Executor::new();
    let x = exec.ctx.terms.mk_fresh_var("x", Sort::String);
    let len_x = exec
        .ctx
        .terms
        .mk_app(Symbol::named("str.len"), vec![x], Sort::Int);
    let zero = exec.ctx.terms.mk_int(BigInt::from(0));
    let ge = exec.ctx.terms.mk_ge(len_x, zero);

    let clauses = exec.lower_dynamic_axiom_to_clauses(ge);

    assert_eq!(clauses, vec![vec![ge]]);
}

#[test]
fn equality_split_clause_includes_guarded_eq_and_neq() {
    let mut exec = Executor::new();
    let mut cache = ExecutorSkolemCache::new();
    let x = exec.ctx.terms.mk_fresh_var("x", Sort::String);
    let y = exec.ctx.terms.mk_fresh_var("y", Sort::String);
    let empty = exec.ctx.terms.mk_string(String::new());
    let x_empty = exec.ctx.terms.mk_eq(x, empty);
    let eq = exec.ctx.terms.mk_eq(x, y);
    let neq = exec.ctx.terms.mk_not(eq);
    let lemma = StringLemma {
        kind: StringLemmaKind::EqualitySplit,
        x,
        y,
        char_offset: 0,
        start_offset: 0,
        reason: vec![TheoryLit::new(x_empty, true)],
    };

    let clauses = exec.create_string_lemma_clauses(&lemma, &mut cache);

    assert_eq!(clauses, vec![vec![exec.ctx.terms.mk_not(x_empty), eq, neq]]);
}

#[test]
fn deq_empty_split_clause_includes_empty_decision() {
    let mut exec = Executor::new();
    let mut cache = ExecutorSkolemCache::new();
    let x = exec.ctx.terms.mk_fresh_var("x", Sort::String);
    let reason = exec.ctx.terms.mk_fresh_var("r", Sort::Bool);
    let empty = exec.ctx.terms.mk_string(String::new());
    let x_empty = exec.ctx.terms.mk_eq(x, empty);
    let x_non_empty = exec.ctx.terms.mk_not(x_empty);
    let lemma = StringLemma {
        kind: StringLemmaKind::DeqEmptySplit,
        x,
        y: empty,
        char_offset: 0,
        start_offset: 0,
        reason: vec![TheoryLit::new(reason, false)],
    };

    let clauses = exec.create_string_lemma_clauses(&lemma, &mut cache);

    assert_eq!(clauses, vec![vec![reason, x_empty, x_non_empty]]);
}

#[test]
fn string_lemma_reduced_terms_substr_reduction_includes_substr_and_concat() {
    let mut exec = Executor::new();
    let mut cache = ExecutorSkolemCache::new();
    let s = exec.ctx.terms.mk_fresh_var("s", Sort::String);
    let one = exec.ctx.terms.mk_int(BigInt::from(1));
    let two = exec.ctx.terms.mk_int(BigInt::from(2));
    let substr =
        exec.ctx
            .terms
            .mk_app(Symbol::named("str.substr"), vec![s, one, two], Sort::String);
    let lemma = StringLemma {
        kind: StringLemmaKind::SubstrReduction,
        x: substr,
        y: exec.ctx.terms.mk_string(String::new()),
        char_offset: 0,
        start_offset: 0,
        reason: Vec::new(),
    };

    let reduced = exec.string_lemma_reduced_terms(&lemma, &mut cache);
    let sk_pre = cache.substr_pre(&mut exec.ctx.terms, substr);
    let sk_result = cache.substr_result(&mut exec.ctx.terms, substr);
    let sk_suffix = cache.substr_suffix(&mut exec.ctx.terms, substr);
    let concat = exec.ctx.terms.mk_app(
        Symbol::named("str.++"),
        vec![sk_pre, sk_result, sk_suffix],
        Sort::String,
    );

    assert_eq!(reduced, vec![substr, concat]);
}

// --- Unit tests for each StringLemmaKind arm (AC1) ---

#[test]
fn length_split_clause_is_tautological_decision() {
    let mut exec = Executor::new();
    let mut cache = ExecutorSkolemCache::new();
    let x = exec.ctx.terms.mk_fresh_var("x", Sort::String);
    let y = exec.ctx.terms.mk_fresh_var("y", Sort::String);
    let lemma = StringLemma {
        kind: StringLemmaKind::LengthSplit,
        x,
        y,
        char_offset: 0,
        start_offset: 0,
        reason: Vec::new(),
    };

    let clauses = exec.create_string_lemma_clauses(&lemma, &mut cache);

    assert_eq!(
        clauses.len(),
        1,
        "LengthSplit must produce exactly one clause"
    );
    assert_eq!(
        clauses[0].len(),
        2,
        "decision clause must be binary: eq ∨ neq"
    );
    let len_x = exec
        .ctx
        .terms
        .mk_app(Symbol::named("str.len"), vec![x], Sort::Int);
    let len_y = exec
        .ctx
        .terms
        .mk_app(Symbol::named("str.len"), vec![y], Sort::Int);
    let eq = exec.ctx.terms.mk_eq(len_x, len_y);
    let neq = exec.ctx.terms.mk_not(eq);
    assert_eq!(clauses[0], vec![eq, neq]);
}

#[test]
fn empty_split_clause_is_tautological_decision() {
    let mut exec = Executor::new();
    let mut cache = ExecutorSkolemCache::new();
    let x = exec.ctx.terms.mk_fresh_var("x", Sort::String);
    let lemma = StringLemma {
        kind: StringLemmaKind::EmptySplit,
        x,
        y: exec.ctx.terms.mk_string(String::new()),
        char_offset: 0,
        start_offset: 0,
        reason: Vec::new(),
    };

    let clauses = exec.create_string_lemma_clauses(&lemma, &mut cache);

    assert_eq!(
        clauses.len(),
        1,
        "EmptySplit must produce exactly one clause"
    );
    let empty = exec.ctx.terms.mk_string(String::new());
    let eq = exec.ctx.terms.mk_eq(x, empty);
    let neq = exec.ctx.terms.mk_not(eq);
    assert_eq!(clauses[0], vec![eq, neq]);
}

#[test]
fn const_split_clause_has_empty_guard_and_concat_split() {
    let mut exec = Executor::new();
    let mut cache = ExecutorSkolemCache::new();
    let x = exec.ctx.terms.mk_fresh_var("x", Sort::String);
    let y = exec.ctx.terms.mk_string("abc".to_string());
    let lemma = StringLemma {
        kind: StringLemmaKind::ConstSplit,
        x,
        y,
        char_offset: 0,
        start_offset: 0,
        reason: Vec::new(),
    };

    let clauses = exec.create_string_lemma_clauses(&lemma, &mut cache);

    // Primary clause: x="" ∨ x=str.++("a", k)
    assert!(
        clauses.len() >= 2,
        "ConstSplit must produce primary + bridge clauses"
    );
    let primary = &clauses[0];
    assert_eq!(
        primary.len(),
        2,
        "no-reason ConstSplit primary must be binary"
    );
    let empty = exec.ctx.terms.mk_string(String::new());
    let x_eq_empty = exec.ctx.terms.mk_eq(x, empty);
    assert_eq!(primary[0], x_eq_empty, "first literal must be x=\"\" guard");
    // Second literal: x = str.++("a", k) — verify it's an equality with x on lhs
    let eq_term = primary[1];
    match exec.ctx.terms.get(eq_term) {
        TermData::App(sym, args) if sym.name() == "=" => {
            assert_eq!(args[0], x, "equality lhs must be x");
        }
        _ => panic!("second literal must be an equality"),
    }
}

#[test]
fn const_split_with_reason_guard_prepends_negated_reason() {
    let mut exec = Executor::new();
    let mut cache = ExecutorSkolemCache::new();
    let x = exec.ctx.terms.mk_fresh_var("x", Sort::String);
    let y = exec.ctx.terms.mk_string("hello".to_string());
    let guard_var = exec.ctx.terms.mk_fresh_var("g", Sort::Bool);
    let lemma = StringLemma {
        kind: StringLemmaKind::ConstSplit,
        x,
        y,
        char_offset: 0,
        start_offset: 0,
        reason: vec![TheoryLit::new(guard_var, true)],
    };

    let clauses = exec.create_string_lemma_clauses(&lemma, &mut cache);

    let primary = &clauses[0];
    // First literal should be ¬guard_var (negated true reason)
    assert_eq!(
        primary[0],
        exec.ctx.terms.mk_not(guard_var),
        "reason guard must prepend negated literal"
    );
    // Remaining: x="" ∨ x=str.++("h", k)
    assert_eq!(
        primary.len(),
        3,
        "guarded ConstSplit primary must have guard + empty + concat"
    );
}

#[test]
fn const_split_at_offset_uses_correct_character() {
    let mut exec = Executor::new();
    let mut cache = ExecutorSkolemCache::new();
    let x = exec.ctx.terms.mk_fresh_var("x", Sort::String);
    let y = exec.ctx.terms.mk_string("abc".to_string());
    let lemma = StringLemma {
        kind: StringLemmaKind::ConstSplit,
        x,
        y,
        char_offset: 1, // should use 'b'
        start_offset: 0,
        reason: Vec::new(),
    };

    let clauses = exec.create_string_lemma_clauses(&lemma, &mut cache);

    let primary = &clauses[0];
    // x = str.++("b", k) — extract the first char of the concat
    let eq_term = primary[1];
    let concat = match exec.ctx.terms.get(eq_term) {
        TermData::App(sym, args) if sym.name() == "=" => {
            assert_eq!(args[0], x, "equality lhs must be x");
            args[1]
        }
        _ => panic!("second literal must be an equality"),
    };
    let first_concat_arg = match exec.ctx.terms.get(concat) {
        TermData::App(csym, cargs) if csym.name() == "str.++" => cargs[0],
        _ => panic!("rhs of equality must be str.++ concat"),
    };
    let b_term = exec.ctx.terms.mk_string("b".to_string());
    assert_eq!(
        first_concat_arg, b_term,
        "char_offset=1 must select 'b' from 'abc'"
    );
}

#[test]
fn var_split_clause_has_len_guard_and_both_concat_directions() {
    let mut exec = Executor::new();
    let mut cache = ExecutorSkolemCache::new();
    let x = exec.ctx.terms.mk_fresh_var("x", Sort::String);
    let y = exec.ctx.terms.mk_fresh_var("y", Sort::String);
    let lemma = StringLemma {
        kind: StringLemmaKind::VarSplit,
        x,
        y,
        char_offset: 0,
        start_offset: 0,
        reason: Vec::new(),
    };

    let clauses = exec.create_string_lemma_clauses(&lemma, &mut cache);

    // Primary clause: x="" ∨ y="" ∨ len(x)=len(y) ∨ x=y++k ∨ y=x++k
    assert!(
        clauses.len() >= 2,
        "VarSplit must produce primary + bridge clauses"
    );
    let primary = &clauses[0];
    // No reason guards, so: x="" ∨ y="" ∨ len_eq ∨ eq_xy ∨ eq_yx = 5 literals
    assert_eq!(
        primary.len(),
        5,
        "no-reason VarSplit primary must have 5 literals: x=\"\", y=\"\", len_eq, x=y++k, y=x++k"
    );

    // Verify the emptiness escape literals
    let empty = exec.ctx.terms.mk_string(String::new());
    let x_empty = exec.ctx.terms.mk_eq(x, empty);
    let y_empty = exec.ctx.terms.mk_eq(y, empty);
    assert_eq!(primary[0], x_empty, "first literal must be x=\"\"");
    assert_eq!(primary[1], y_empty, "second literal must be y=\"\"");

    // Verify len(x)=len(y) guard
    let len_x = exec
        .ctx
        .terms
        .mk_app(Symbol::named("str.len"), vec![x], Sort::Int);
    let len_y = exec
        .ctx
        .terms
        .mk_app(Symbol::named("str.len"), vec![y], Sort::Int);
    let len_eq = exec.ctx.terms.mk_eq(len_x, len_y);
    assert_eq!(primary[2], len_eq, "third literal must be len(x)=len(y)");
}

#[test]
fn contains_positive_clause_is_decomposition_equality() {
    let mut exec = Executor::new();
    let mut cache = ExecutorSkolemCache::new();
    let x = exec.ctx.terms.mk_fresh_var("x", Sort::String);
    let y = exec.ctx.terms.mk_fresh_var("y", Sort::String);
    let lemma = StringLemma {
        kind: StringLemmaKind::ContainsPositive,
        x,
        y,
        char_offset: 0,
        start_offset: 0,
        reason: Vec::new(),
    };

    let clauses = exec.create_string_lemma_clauses(&lemma, &mut cache);

    // Primary clause: x = str.++(sk_pre, y, sk_post)
    assert!(
        !clauses.is_empty(),
        "ContainsPositive must produce at least the primary clause"
    );
    let primary = &clauses[0];
    assert_eq!(primary.len(), 1, "primary must be a unit clause");
    // The unit literal is x = str.++(sk_pre, y, sk_post)
    let concat_rhs = match exec.ctx.terms.get(primary[0]) {
        TermData::App(sym, args) if sym.name() == "=" => {
            assert_eq!(args[0], x, "equality lhs must be x");
            args[1]
        }
        _ => panic!("primary literal must be an equality"),
    };
    match exec.ctx.terms.get(concat_rhs) {
        TermData::App(csym, cargs) if csym.name() == "str.++" => {
            assert_eq!(cargs.len(), 3, "concat must have 3 args: pre, y, post");
            assert_eq!(cargs[1], y, "middle concat arg must be y");
        }
        _ => panic!("rhs must be str.++ concat"),
    }
    // Should also have bridge axioms for the two skolems (6 clauses: 3 per skolem)
    assert!(
        clauses.len() >= 7,
        "ContainsPositive must have primary + 2×3 bridge clauses, got {}",
        clauses.len()
    );
}

#[test]
fn const_unify_clause_has_prefix_equality_and_length_axiom() {
    let mut exec = Executor::new();
    let mut cache = ExecutorSkolemCache::new();
    let x = exec.ctx.terms.mk_fresh_var("x", Sort::String);
    let y = exec.ctx.terms.mk_string("hello".to_string());
    let lemma = StringLemma {
        kind: StringLemmaKind::ConstUnify,
        x,
        y,
        char_offset: 3, // prefix "hel"
        start_offset: 0,
        reason: Vec::new(),
    };

    let clauses = exec.create_string_lemma_clauses(&lemma, &mut cache);

    // No reason: primary clause is unit [x = "hel"], plus length axiom [len("hel") = 3]
    assert_eq!(
        clauses.len(),
        2,
        "no-reason ConstUnify must produce primary + length axiom"
    );
    let prefix = exec.ctx.terms.mk_string("hel".to_string());
    let eq = exec.ctx.terms.mk_eq(x, prefix);
    assert_eq!(
        clauses[0],
        vec![eq],
        "primary clause must assert x = prefix"
    );
    // Length axiom: len("hel") = 3
    let len_prefix = exec
        .ctx
        .terms
        .mk_app(Symbol::named("str.len"), vec![prefix], Sort::Int);
    let three = exec.ctx.terms.mk_int(BigInt::from(3));
    let len_eq = exec.ctx.terms.mk_eq(len_prefix, three);
    assert_eq!(
        clauses[1],
        vec![len_eq],
        "second clause must be len(prefix)=3"
    );
}

#[test]
fn deq_first_char_eq_split_clause_splits_on_first_character() {
    let mut exec = Executor::new();
    let mut cache = ExecutorSkolemCache::new();
    let x = exec.ctx.terms.mk_fresh_var("x", Sort::String);
    let y = exec.ctx.terms.mk_string("abc".to_string());
    let lemma = StringLemma {
        kind: StringLemmaKind::DeqFirstCharEqSplit,
        x,
        y,
        char_offset: 0,
        start_offset: 0,
        reason: Vec::new(),
    };

    let clauses = exec.create_string_lemma_clauses(&lemma, &mut cache);

    assert_eq!(
        clauses.len(),
        1,
        "DeqFirstCharEqSplit must produce exactly one clause"
    );
    let a_term = exec.ctx.terms.mk_string("a".to_string());
    let eq = exec.ctx.terms.mk_eq(x, a_term);
    let neq = exec.ctx.terms.mk_not(eq);
    assert_eq!(
        clauses[0],
        vec![eq, neq],
        "clause must be x=\"a\" ∨ x≠\"a\""
    );
}

#[test]
fn substr_reduction_clause_has_ite_decomposition_and_bridge() {
    let mut exec = Executor::new();
    let mut cache = ExecutorSkolemCache::new();
    let s = exec.ctx.terms.mk_fresh_var("s", Sort::String);
    let one = exec.ctx.terms.mk_int(BigInt::from(1));
    let two = exec.ctx.terms.mk_int(BigInt::from(2));
    let substr =
        exec.ctx
            .terms
            .mk_app(Symbol::named("str.substr"), vec![s, one, two], Sort::String);
    let lemma = StringLemma {
        kind: StringLemmaKind::SubstrReduction,
        x: substr,
        y: exec.ctx.terms.mk_string(String::new()),
        char_offset: 0,
        start_offset: 0,
        reason: Vec::new(),
    };

    let clauses = exec.create_string_lemma_clauses(&lemma, &mut cache);

    // SubstrReduction produces ITE-lowered clauses + bridge equality + 3×3 bridge axioms
    assert!(
        clauses.len() >= 2,
        "SubstrReduction must produce multiple clauses, got {}",
        clauses.len()
    );
    // All clauses must be non-empty (no false-UNSAT from empty clauses)
    for (i, c) in clauses.iter().enumerate() {
        assert!(!c.is_empty(), "clause {i} must be non-empty");
    }
}

// --- Unit tests for collect_str_len_axioms_from_roots (AC: #6356) ---

#[test]
fn collect_str_len_axioms_simple_len_emits_non_negativity_and_biconditional() {
    let mut exec = Executor::new();
    let x = exec.ctx.terms.mk_fresh_var("x", Sort::String);
    let len_x = exec
        .ctx
        .terms
        .mk_app(Symbol::named("str.len"), vec![x], Sort::Int);

    let axioms = exec.collect_str_len_axioms_from_roots(&[len_x]);

    // Must emit at least 3 axioms:
    //   1. str.len(x) >= 0
    //   2. str.len(x) = 0 => x = ""
    //   3. x = "" => str.len(x) = 0
    assert!(
        axioms.len() >= 3,
        "simple str.len(x) must emit >= 3 axioms, got {}",
        axioms.len()
    );

    // Axiom 1: non-negativity
    let zero = exec.ctx.terms.mk_int(BigInt::from(0));
    let ge = exec.ctx.terms.mk_ge(len_x, zero);
    assert_eq!(axioms[0], ge, "first axiom must be str.len(x) >= 0");
}

#[test]
fn collect_str_len_axioms_constant_len_emits_exact_value() {
    let mut exec = Executor::new();
    let abc = exec.ctx.terms.mk_string("abc".to_string());
    let len_abc = exec
        .ctx
        .terms
        .mk_app(Symbol::named("str.len"), vec![abc], Sort::Int);

    let axioms = exec.collect_str_len_axioms_from_roots(&[len_abc]);

    // Must include: str.len("abc") = 3
    let three = exec.ctx.terms.mk_int(BigInt::from(3));
    let expected_eq = exec.ctx.terms.mk_eq(len_abc, three);
    assert!(
        axioms.contains(&expected_eq),
        "constant len must include str.len(\"abc\") = 3"
    );
}

#[test]
fn collect_str_len_axioms_concat_len_emits_decomposition() {
    let mut exec = Executor::new();
    let a = exec.ctx.terms.mk_fresh_var("a", Sort::String);
    let b = exec.ctx.terms.mk_fresh_var("b", Sort::String);
    let concat = exec
        .ctx
        .terms
        .mk_app(Symbol::named("str.++"), vec![a, b], Sort::String);
    let len_concat = exec
        .ctx
        .terms
        .mk_app(Symbol::named("str.len"), vec![concat], Sort::Int);

    let axioms = exec.collect_str_len_axioms_from_roots(&[len_concat]);

    // Must include: str.len(str.++(a,b)) = str.len(a) + str.len(b)
    let len_a = exec
        .ctx
        .terms
        .mk_app(Symbol::named("str.len"), vec![a], Sort::Int);
    let len_b = exec
        .ctx
        .terms
        .mk_app(Symbol::named("str.len"), vec![b], Sort::Int);
    let sum = exec.ctx.terms.mk_add(vec![len_a, len_b]);
    let expected_eq = exec.ctx.terms.mk_eq(len_concat, sum);
    assert!(
        axioms.contains(&expected_eq),
        "concat len must include decomposition axiom"
    );

    // Must also include non-negativity for concat args
    let zero_a = exec.ctx.terms.mk_int(BigInt::from(0));
    let ge_a = exec.ctx.terms.mk_ge(len_a, zero_a);
    assert!(
        axioms.contains(&ge_a),
        "concat len must include str.len(a) >= 0"
    );
}

#[test]
fn collect_str_len_axioms_contains_emits_length_bound() {
    let mut exec = Executor::new();
    let x = exec.ctx.terms.mk_fresh_var("x", Sort::String);
    let y = exec.ctx.terms.mk_fresh_var("y", Sort::String);
    let contains = exec
        .ctx
        .terms
        .mk_app(Symbol::named("str.contains"), vec![x, y], Sort::Bool);

    let axioms = exec.collect_str_len_axioms_from_roots(&[contains]);

    // Must include: str.contains(x, y) => str.len(x) >= str.len(y)
    let len_x = exec
        .ctx
        .terms
        .mk_app(Symbol::named("str.len"), vec![x], Sort::Int);
    let len_y = exec
        .ctx
        .terms
        .mk_app(Symbol::named("str.len"), vec![y], Sort::Int);
    let ge = exec.ctx.terms.mk_ge(len_x, len_y);
    let implies = exec.ctx.terms.mk_implies(contains, ge);
    assert!(
        axioms.contains(&implies),
        "contains must emit containment length bound implication"
    );
}

#[test]
fn collect_str_len_axioms_prefixof_emits_length_bound() {
    let mut exec = Executor::new();
    let s = exec.ctx.terms.mk_fresh_var("s", Sort::String);
    let x = exec.ctx.terms.mk_fresh_var("x", Sort::String);
    // str.prefixof(s, x): s is prefix of x
    let prefixof = exec
        .ctx
        .terms
        .mk_app(Symbol::named("str.prefixof"), vec![s, x], Sort::Bool);

    let axioms = exec.collect_str_len_axioms_from_roots(&[prefixof]);

    // Must include: str.prefixof(s, x) => str.len(x) >= str.len(s)
    // Note: container=x (args[1]), contained=s (args[0])
    let len_x = exec
        .ctx
        .terms
        .mk_app(Symbol::named("str.len"), vec![x], Sort::Int);
    let len_s = exec
        .ctx
        .terms
        .mk_app(Symbol::named("str.len"), vec![s], Sort::Int);
    let ge = exec.ctx.terms.mk_ge(len_x, len_s);
    let implies = exec.ctx.terms.mk_implies(prefixof, ge);
    assert!(
        axioms.contains(&implies),
        "prefixof must emit containment length bound implication"
    );
}

#[test]
fn collect_str_len_axioms_to_int_emits_lower_bound() {
    let mut exec = Executor::new();
    let x = exec.ctx.terms.mk_fresh_var("x", Sort::String);
    let to_int = exec
        .ctx
        .terms
        .mk_app(Symbol::named("str.to_int"), vec![x], Sort::Int);

    let axioms = exec.collect_str_len_axioms_from_roots(&[to_int]);

    // Must include: str.to_int(x) >= -1
    let minus_one = exec.ctx.terms.mk_int(BigInt::from(-1));
    let ge = exec.ctx.terms.mk_ge(to_int, minus_one);
    assert!(
        axioms.contains(&ge),
        "str.to_int must emit >= -1 lower bound"
    );
}

#[test]
fn collect_str_len_axioms_to_code_emits_bounds_and_conditional() {
    let mut exec = Executor::new();
    let x = exec.ctx.terms.mk_fresh_var("x", Sort::String);
    let to_code = exec
        .ctx
        .terms
        .mk_app(Symbol::named("str.to_code"), vec![x], Sort::Int);

    let axioms = exec.collect_str_len_axioms_from_roots(&[to_code]);

    // Must include: str.to_code(x) >= -1
    let minus_one = exec.ctx.terms.mk_int(BigInt::from(-1));
    let ge_lower = exec.ctx.terms.mk_ge(to_code, minus_one);
    assert!(
        axioms.contains(&ge_lower),
        "str.to_code must emit >= -1 lower bound"
    );

    // Must include: str.to_code(x) <= 196607
    let upper = exec.ctx.terms.mk_int(BigInt::from(196_607));
    let le_upper = exec.ctx.terms.mk_le(to_code, upper);
    assert!(
        axioms.contains(&le_upper),
        "str.to_code must emit <= 196607 upper bound"
    );

    // Must include conditional axioms (4 total: lower, upper, len=1 => >=0, len!=1 => =-1)
    assert!(
        axioms.len() >= 4,
        "str.to_code must emit at least 4 axioms (bounds + conditionals), got {}",
        axioms.len()
    );
}

#[test]
fn collect_str_len_axioms_indexof_emits_bounds() {
    let mut exec = Executor::new();
    let x = exec.ctx.terms.mk_fresh_var("x", Sort::String);
    let y = exec.ctx.terms.mk_fresh_var("y", Sort::String);
    let n = exec.ctx.terms.mk_int(BigInt::from(0));
    let indexof = exec
        .ctx
        .terms
        .mk_app(Symbol::named("str.indexof"), vec![x, y, n], Sort::Int);

    let axioms = exec.collect_str_len_axioms_from_roots(&[indexof]);

    // Must include: str.indexof(x, y, n) >= -1
    let minus_one = exec.ctx.terms.mk_int(BigInt::from(-1));
    let ge_lower = exec.ctx.terms.mk_ge(indexof, minus_one);
    assert!(
        axioms.contains(&ge_lower),
        "str.indexof must emit >= -1 lower bound"
    );

    // Must include: str.indexof(x, y, n) <= str.len(x)
    let len_x = exec
        .ctx
        .terms
        .mk_app(Symbol::named("str.len"), vec![x], Sort::Int);
    let le_upper = exec.ctx.terms.mk_le(indexof, len_x);
    assert!(
        axioms.contains(&le_upper),
        "str.indexof must emit <= str.len(x) upper bound"
    );
}

#[test]
fn collect_str_len_axioms_string_equality_emits_length_implication() {
    let mut exec = Executor::new();
    let x = exec.ctx.terms.mk_fresh_var("x", Sort::String);
    let y = exec.ctx.terms.mk_fresh_var("y", Sort::String);
    let eq = exec.ctx.terms.mk_eq(x, y);

    let axioms = exec.collect_str_len_axioms_from_roots(&[eq]);

    // Must include: (= x y) => (= (str.len x) (str.len y))
    let len_x = exec
        .ctx
        .terms
        .mk_app(Symbol::named("str.len"), vec![x], Sort::Int);
    let len_y = exec
        .ctx
        .terms
        .mk_app(Symbol::named("str.len"), vec![y], Sort::Int);
    let len_eq = exec.ctx.terms.mk_eq(len_x, len_y);
    let implies = exec.ctx.terms.mk_implies(eq, len_eq);
    assert!(
        axioms.contains(&implies),
        "string equality must emit length equality implication"
    );
}

#[test]
fn collect_str_len_axioms_equality_with_constant_emits_concrete_length() {
    let mut exec = Executor::new();
    let x = exec.ctx.terms.mk_fresh_var("x", Sort::String);
    let hello = exec.ctx.terms.mk_string("hello".to_string());
    let eq = exec.ctx.terms.mk_eq(x, hello);

    let axioms = exec.collect_str_len_axioms_from_roots(&[eq]);

    // Must include: (= x "hello") => (= (str.len x) 5)
    let len_x = exec
        .ctx
        .terms
        .mk_app(Symbol::named("str.len"), vec![x], Sort::Int);
    let five = exec.ctx.terms.mk_int(BigInt::from(5));
    let len_eq = exec.ctx.terms.mk_eq(len_x, five);
    let implies = exec.ctx.terms.mk_implies(eq, len_eq);
    assert!(
        axioms.contains(&implies),
        "equality with constant must emit concrete length implication"
    );
}

#[test]
fn collect_str_len_axioms_equality_with_concat_emits_constant_part_lengths() {
    let mut exec = Executor::new();
    let x = exec.ctx.terms.mk_fresh_var("x", Sort::String);
    let y = exec.ctx.terms.mk_fresh_var("y", Sort::String);
    let ab = exec.ctx.terms.mk_string("ab".to_string());
    let concat = exec
        .ctx
        .terms
        .mk_app(Symbol::named("str.++"), vec![ab, y], Sort::String);
    let eq = exec.ctx.terms.mk_eq(concat, x);

    let axioms = exec.collect_str_len_axioms_from_roots(&[eq]);

    let len_ab = exec
        .ctx
        .terms
        .mk_app(Symbol::named("str.len"), vec![ab], Sort::Int);
    let two = exec.ctx.terms.mk_int(BigInt::from(2));
    let len_eq = exec.ctx.terms.mk_eq(len_ab, two);
    assert!(
        axioms.contains(&len_eq),
        "concat-length backfill must emit concrete lengths for constant concat parts"
    );
}

#[test]
fn collect_str_len_axioms_deduplicates_str_len_args() {
    let mut exec = Executor::new();
    let x = exec.ctx.terms.mk_fresh_var("x", Sort::String);
    let len_x = exec
        .ctx
        .terms
        .mk_app(Symbol::named("str.len"), vec![x], Sort::Int);
    // Create a second str.len(x) — should be deduplicated
    let len_x2 = exec
        .ctx
        .terms
        .mk_app(Symbol::named("str.len"), vec![x], Sort::Int);

    let axioms = exec.collect_str_len_axioms_from_roots(&[len_x, len_x2]);

    // Non-negativity axiom should appear exactly once
    let zero = exec.ctx.terms.mk_int(BigInt::from(0));
    let ge = exec.ctx.terms.mk_ge(len_x, zero);
    let count = axioms.iter().filter(|a| **a == ge).count();
    assert_eq!(
        count, 1,
        "duplicate str.len(x) must be deduplicated, non-negativity appeared {count} times"
    );
}

#[test]
fn collect_str_len_axioms_ground_extf_emits_equality() {
    let mut exec = Executor::new();
    let hello = exec.ctx.terms.mk_string("hello".to_string());
    let zero = exec.ctx.terms.mk_int(BigInt::from(0));
    // str.at("hello", 0) should ground-evaluate to "h"
    let str_at = exec
        .ctx
        .terms
        .mk_app(Symbol::named("str.at"), vec![hello, zero], Sort::String);

    let axioms = exec.collect_str_len_axioms_from_roots(&[str_at]);

    // Must include: str.at("hello", 0) = "h"
    let h = exec.ctx.terms.mk_string("h".to_string());
    let expected_eq = exec.ctx.terms.mk_eq(str_at, h);
    assert!(
        axioms.contains(&expected_eq),
        "ground extf must emit equality: str.at(\"hello\", 0) = \"h\""
    );
}
