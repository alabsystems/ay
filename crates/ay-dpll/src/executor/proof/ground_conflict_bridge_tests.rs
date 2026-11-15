// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

fn comparison(
    terms: &mut TermStore,
    name: &str,
    left: TermId,
    right: TermId,
    negative: bool,
) -> TermId {
    let relation = terms.mk_app(Symbol::named(name), vec![left, right], Sort::Bool);
    if negative {
        terms.mk_not_raw(relation)
    } else {
        relation
    }
}

/// The traced mixed clause: equality of the indices transports the array read
/// to `w`; nonnegativity contradicts its negative value. The two index bounds
/// are redundant. The switches construct actual countermodel twins below.
fn fixture(nonnegative_value: bool, same_array: bool) -> (Executor, Vec<TermId>) {
    let mut exec = Executor::new();
    let terms = &mut exec.ctx.terms;
    let array_sort = Sort::Array(Box::new(ay_core::ArraySort::new(Sort::Int, Sort::Int)));
    let array = terms.mk_var("bridge_array", array_sort.clone());
    let value_array = if same_array {
        array
    } else {
        terms.mk_var("bridge_other_array", array_sort)
    };
    let w = terms.mk_var("bridge_w", Sort::Int);
    let j = terms.mk_var("bridge_j", Sort::Int);
    let zero = terms.mk_int(0.into());
    let one = terms.mk_int(1.into());
    let two = terms.mk_int(2.into());
    let three = terms.mk_int(3.into());
    let read_two = terms.mk_app(Symbol::named("select"), vec![value_array, two], Sort::Int);
    let read_j = terms.mk_app(Symbol::named("select"), vec![array, j], Sort::Int);
    let value_eq = terms.mk_eq(w, read_two);
    let value_lit = terms.mk_not_raw(value_eq);
    let bound = if nonnegative_value {
        comparison(terms, "<=", zero, w, true)
    } else {
        comparison(terms, "<=", w, zero, true)
    };
    let negative_read = comparison(terms, "<", read_j, zero, true);
    let index_eq = terms.mk_eq(two, j);
    let index_lit = terms.mk_not_raw(index_eq);
    let upper = comparison(terms, "<", j, three, true);
    let lower = comparison(terms, "<=", j, one, false);
    (
        exec,
        vec![value_lit, bound, negative_read, index_lit, upper, lower],
    )
}

fn noise(terms: &mut TermStore, index: usize) -> TermId {
    let x = terms.mk_var(format!("bridge_noise_{index}"), Sort::Int);
    let zero = terms.mk_int(0.into());
    comparison(terms, "<=", zero, x, true)
}

/// Check the actual emitted theorem, including its exact original conclusion.
/// It has no assumptions and grants no problem premises.
fn checked_bridge(exec: &mut Executor, clause: &[TermId]) -> Proof {
    let plan = plan_euf_chain_farkas_bridge(&mut exec.ctx.terms, clause)
        .expect("the equality/arithmetic contradiction must be recognized");
    assert!(plan.la_clause.len() <= MAX_GROUND_CONFLICT_BRIDGE_RELS + 1);
    let mut steps = Vec::new();
    let (last, conclusion) = emit_euf_chain_farkas_bridge(&mut exec.ctx.terms, &mut steps, &plan);
    assert_eq!(last, ProofId(steps.len() as u32 - 1));
    assert!(clauses_match_as_sets_local(&conclusion, clause));
    assert!(!steps
        .iter()
        .any(|step| matches!(step, ProofStep::Assume(_))));
    let mut proof = Proof::new();
    proof.steps = steps;
    let checked = ay_proof::authenticate_premise_clauses_strict_with_context(
        &proof,
        &exec.ctx.terms,
        None,
        None,
        &[],
    )
    .expect("all theorem steps must strictly authenticate without assumptions");
    assert_eq!(checked.clause(last), Some(conclusion.as_slice()));
    proof
}

#[test]
fn redundant_arithmetic_guards_have_a_strict_exact_clause_derivation() {
    let (mut exec, clause) = fixture(true, true);
    let mut proof = checked_bridge(&mut exec, &clause);
    let Some(ProofStep::Step {
        rule: AletheRule::Weakening,
        clause: weakened,
        ..
    }) = proof.steps.last_mut()
    else {
        panic!("unused guards must be restored by explicit weakening");
    };
    // Dropping a consumed equality premise from the final weakening would
    // assert a stronger, false clause. The checker must refuse that tampering.
    weakened.retain(|&lit| lit != clause[0]);
    assert!(ay_proof::authenticate_premise_clauses_strict_with_context(
        &proof,
        &exec.ctx.terms,
        None,
        None,
        &[],
    )
    .is_err());
}

#[test]
fn useful_relations_after_three_unrelated_guards_are_found() {
    let (mut exec, base) = fixture(true, true);
    let mut clause = vec![base[0], base[3]];
    for index in 0..3 {
        clause.push(noise(&mut exec.ctx.terms, index));
    }
    clause.extend([base[1], base[2]]);
    checked_bridge(&mut exec, &clause);
}

#[test]
fn a_nonpositive_value_does_not_gain_a_false_bridge() {
    // Countermodel of the clause: j=2, w=-1, and the array constantly -1.
    let (mut exec, clause) = fixture(false, true);
    assert!(plan_euf_chain_farkas_bridge(&mut exec.ctx.terms, &clause).is_none());
}

#[test]
fn unrelated_arrays_do_not_gain_congruence_authority() {
    // Countermodel: j=2, w=0, other_array constantly 0, array constantly -1.
    let (mut exec, clause) = fixture(true, false);
    assert!(plan_euf_chain_farkas_bridge(&mut exec.ctx.terms, &clause).is_none());
}

#[test]
fn subset_search_keeps_one_exhaustible_allowance() {
    let (mut exec, base) = fixture(true, true);
    let mut clause = vec![base[0], base[3]];
    for index in 0..12 {
        clause.push(noise(&mut exec.ctx.terms, index));
    }
    clause.extend([base[1], base[2]]);
    assert_eq!(clause.len(), MAX_GROUND_CONFLICT_DECOMP_LITERALS);
    // The first triple containing both necessary comparisons is number 78,
    // beyond the shared 64 even before any head/Farkas probes are charged.
    assert!(plan_euf_chain_farkas_bridge(&mut exec.ctx.terms, &clause).is_none());

    let selected = [base[1], base[2], base[4]];
    let (value_inner, negative) = strip_not_local(&exec.ctx.terms, base[0]);
    assert!(negative);
    let (a, b) = decode_eq_local(&exec.ctx.terms, value_inner).unwrap();
    let (index_inner, _) = strip_not_local(&exec.ctx.terms, base[3]);
    let (c, d) = decode_eq_local(&exec.ctx.terms, index_inner).unwrap();
    let edges = [(a, b, base[0]), (c, d, base[3])];
    let mut remaining = 0;
    assert!(plan_euf_chain_farkas_bridge_relations(
        &mut exec.ctx.terms,
        &base,
        &selected,
        &edges,
        &mut remaining,
    )
    .is_none());
    assert_eq!(remaining, 0);
}

#[test]
fn original_clause_width_limit_still_applies() {
    let (mut exec, mut clause) = fixture(true, true);
    for index in 0..10 {
        clause.push(noise(&mut exec.ctx.terms, index));
    }
    assert_eq!(clause.len(), MAX_GROUND_CONFLICT_DECOMP_LITERALS);
    checked_bridge(&mut exec, &clause);
    clause.push(noise(&mut exec.ctx.terms, 10));
    assert!(plan_euf_chain_farkas_bridge(&mut exec.ctx.terms, &clause).is_none());
}

#[test]
fn unsupported_literals_and_duplicates_still_decline() {
    let (mut exec, mut clause) = fixture(true, true);
    clause.push(exec.ctx.terms.mk_var("unrelated_bool", Sort::Bool));
    assert!(plan_euf_chain_farkas_bridge(&mut exec.ctx.terms, &clause).is_none());
    let (mut exec, mut clause) = fixture(true, true);
    clause.push(clause[0]);
    assert!(plan_euf_chain_farkas_bridge(&mut exec.ctx.terms, &clause).is_none());
}
