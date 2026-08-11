// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Scope tests for the certified-reconstruction override purge.
//!
//! The purge exists so that one internal term cannot reach the Alethe printer
//! under two spellings. It must remove exactly the stale spellings the
//! committed proof would print — no more (an unrelated assertion keeps the
//! problem file's syntax) and no fewer (a spelling reached only through a
//! clause's SUBTERMS is exactly the one that collided), and only once the
//! strict checker has actually accepted the candidate.

use super::*;

use ay_core::kani_compat::DetHashMap;
use ay_frontend::command::{Command, Sort as FrontendSort};

fn declare_bv8(executor: &mut Executor, name: &str) -> TermId {
    executor
        .ctx
        .process_command(&Command::DeclareConst(
            name.to_string(),
            FrontendSort::Indexed(
                "BitVec".to_string(),
                vec![FrontendIndex::Numeral("8".to_string())],
            ),
        ))
        .expect("fixture declaration succeeds");
    executor
        .ctx
        .elaborate_surface_subterm(&FrontendTerm::Symbol(name.to_string()))
        .expect("declared fixture symbol elaborates")
}

/// `(= <var> #x10)` plus the surface spellings an ordinary export would have
/// collected for it and for its bitvector operand.
fn pinned_equality(executor: &mut Executor, name: &str) -> (TermId, TermId, TermId) {
    let var = declare_bv8(executor, name);
    let constant = executor.ctx.terms.mk_bitvec(BigInt::from(0x10), 8);
    let equality = executor
        .ctx
        .terms
        .mk_app(Symbol::named("="), vec![var, constant], Sort::Bool);
    (equality, var, constant)
}

#[test]
fn purge_drops_only_the_spellings_the_certified_proof_prints() {
    let mut executor = Executor::new();
    let (printed_equality, printed_var, constant) = pinned_equality(&mut executor, "purge_printed");
    let (other_equality, other_var, _) = pinned_equality(&mut executor, "purge_untouched");

    let mut overrides = DetHashMap::default();
    overrides.insert(printed_equality, "(= purge_printed #x10)".to_string());
    overrides.insert(printed_var, "(bvadd purge_printed #x00)".to_string());
    overrides.insert(constant, "#x10".to_string());
    overrides.insert(other_equality, "(= purge_untouched #x10)".to_string());
    overrides.insert(other_var, "(bvadd purge_untouched #x00)".to_string());
    executor.last_proof_term_overrides = Some(overrides);

    let mut candidate = Proof::new();
    let _ = candidate.add_assume(printed_equality, None);
    executor.purge_surface_overrides_for_certified_proof(&candidate);

    let after = executor
        .last_proof_term_overrides
        .clone()
        .expect("the table survives the purge");
    // The clause literal itself...
    assert!(!after.contains_key(&printed_equality));
    // ...and every operand reached through it: the collision the printer
    // reports is between an enclosing spelling and a separately printed
    // SUBTERM, so stopping at the literal would leave it in place.
    assert!(!after.contains_key(&printed_var));
    assert!(!after.contains_key(&constant));
    // An assertion this reconstruction does not print keeps the problem
    // file's own syntax; the purge is not a blanket `= None`.
    assert_eq!(
        after.get(&other_equality),
        Some(&"(= purge_untouched #x10)".to_string())
    );
    assert_eq!(
        after.get(&other_var),
        Some(&"(bvadd purge_untouched #x00)".to_string())
    );
}

#[test]
fn purge_leaves_a_document_that_has_no_surface_spellings_alone() {
    let mut executor = Executor::new();
    let (equality, _, _) = pinned_equality(&mut executor, "purge_no_table");
    executor.last_proof_term_overrides = None;

    let mut candidate = Proof::new();
    let _ = candidate.add_assume(equality, None);
    executor.purge_surface_overrides_for_certified_proof(&candidate);

    assert!(
        executor.last_proof_term_overrides.is_none(),
        "a document with no surface table already prints canonically"
    );
}

#[test]
fn a_candidate_the_strict_gate_rejects_purges_nothing() {
    let mut executor = Executor::new();
    let (equality, var, _) = pinned_equality(&mut executor, "purge_uncommitted");

    let mut overrides = DetHashMap::default();
    overrides.insert(equality, "(= purge_uncommitted #x10)".to_string());
    overrides.insert(var, "(bvadd purge_uncommitted #x00)".to_string());
    executor.last_proof_term_overrides = Some(overrides.clone());

    // Derives nothing, so `commit_if_strictly_checked` must decline.
    let mut candidate = Proof::new();
    let _ = candidate.add_assume(equality, None);
    let mut proof = Proof::new();
    let _ = proof.add_assume(equality, None);

    assert!(!executor.commit_if_strictly_checked(&mut proof, candidate, &[equality]));
    assert_eq!(
        executor.last_proof_term_overrides,
        Some(overrides),
        "the export table may only change for a proof the strict checker accepted"
    );
}
