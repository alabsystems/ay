// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::{AletheRule, Proof};
use num_bigint::BigInt;

fn eq(terms: &mut TermStore, a: TermId, b: TermId) -> TermId {
    terms.mk_app(Symbol::named("="), vec![a, b], Sort::Bool)
}

struct ArrayChain {
    terms: TermStore,
    left: TermId,
    middle: TermId,
    right: TermId,
    goal: TermId,
    first: TermId,
    second: TermId,
}

fn array_chain() -> ArrayChain {
    let mut terms = TermStore::new();
    let array = Sort::array(Sort::bitvec(64), Sort::bitvec(8));
    let mut memory = terms.mk_var("memory", array.clone());
    let sp = terms.mk_var("sp", Sort::bitvec(64));
    let mut last_key = sp;
    for i in 0..80 {
        // The real frame has both deeply nested address arithmetic and an
        // 80-store prefix. Keep both, rather than reducing it to short keys.
        let mut key = sp;
        for offset in [u64::MAX - 79, 0, 0, 0, (i / 8) * 8, 0, i % 8] {
            let word = terms.mk_bitvec(BigInt::from(offset), 64);
            key = terms.mk_app(Symbol::named("bvadd"), vec![key, word], Sort::bitvec(64));
        }
        let value = terms.mk_bitvec(BigInt::from(i), 8);
        memory = terms.mk_app(
            Symbol::named("store"),
            vec![memory, key, value],
            array.clone(),
        );
        last_key = key;
    }
    let left = terms.mk_app(
        Symbol::named("select"),
        vec![memory, last_key],
        Sort::bitvec(8),
    );
    let middle = terms.mk_var("middle", Sort::bitvec(8));
    let right = terms.mk_var("right", Sort::bitvec(8));
    let first = eq(&mut terms, left, middle);
    let second = eq(&mut terms, middle, right);
    let goal = eq(&mut terms, left, right);
    ArrayChain {
        terms,
        left,
        middle,
        right,
        goal,
        first,
        second,
    }
}

#[test]
fn deep_array_transitivity_uses_the_existing_surface_budget() {
    let f = array_chain();
    let printer = AlethePrinter::new_with_overrides_and_budget(&f.terms, None, Some(1024 * 1024));
    let text = printer.format_term(f.goal);
    assert!(text.len() > 30_000, "exercise the original prefix scale");
    assert!(!printer.work_budget_exhausted());
    eprintln!(
        "STREAMED_ARRAY_TRANS goal_bytes={} work={}",
        text.len(),
        printer.work_used()
    );
    assert!(trans_step_surface_is_supported(
        &f.terms,
        &[f.goal],
        &[&[f.first], &[f.second]],
        None,
    ));
}

#[test]
fn deep_array_transitivity_exports_a_complete_checked_proof() {
    let mut f = array_chain();
    let negative = f.terms.mk_not_raw(f.goal);
    let mut proof = Proof::new();
    let first = proof.add_assume(f.first, None);
    let second = proof.add_assume(f.second, None);
    let negative_id = proof.add_assume(negative, None);
    let trans = proof.add_rule_step(
        AletheRule::Trans,
        vec![f.goal],
        vec![first, second],
        Vec::new(),
    );
    proof.add_resolution(Vec::new(), f.goal, trans, negative_id);
    crate::check_proof_strict(&proof, &f.terms).expect("native transitivity and resolution");
    let document = crate::try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &f.terms,
        &[f.first, f.second, negative],
        None,
    )
    .expect("complete production export within unchanged bounds");
    assert!(document.contains(":rule trans"));
    assert!(!document.contains(":rule hole") && !document.contains(":rule trust"));
    let declarations = "(set-logic QF_ABV)\n(declare-const memory (Array (_ BitVec 64) (_ BitVec 8)))\n(declare-const sp (_ BitVec 64))\n(declare-const middle (_ BitVec 8))\n(declare-const right (_ BitVec 8))\n";
    let first = crate::format_term_alethe(&f.terms, f.first);
    let second = crate::format_term_alethe(&f.terms, f.second);
    let negative = crate::format_term_alethe(&f.terms, negative);
    let problem = format!(
        "{declarations}(assert {first})\n(assert {second})\n(assert {negative})\n(check-sat)\n"
    );
    capture("deep-array-trans", &problem, &document);
    // Removing a source premise makes the original satisfiable. The emitted
    // proof still cites that premise, so independent replay must reject it.
    let satisfiable =
        format!("{declarations}(assert {second})\n(assert {negative})\n(check-sat)\n");
    capture("deep-array-trans-missing-premise", &satisfiable, &document);
    eprintln!(
        "STREAMED_ARRAY_TRANS_EXPORT problem_bytes={} proof_bytes={}",
        problem.len(),
        document.len()
    );
}

fn capture(name: &str, problem: &str, proof: &str) {
    use std::io::Write;
    let Some(root) = std::env::var_os("AY_TERM_RENDER_ARTIFACT_DIR") else {
        return;
    };
    let root = std::path::PathBuf::from(root);
    assert!(root.is_absolute());
    std::fs::create_dir_all(&root).unwrap();
    let certificate = serde_json::to_vec(&serde_json::json!({
        "type":"alethe_certificate", "version":"1.0", "problem":problem, "proof":proof,
    }))
    .unwrap();
    for (suffix, data) in [
        ("original.smt2", problem.as_bytes()),
        ("alethe", proof.as_bytes()),
        ("json", certificate.as_slice()),
    ] {
        let mut file = std::fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(root.join(format!("{name}.{suffix}")))
            .unwrap();
        file.write_all(data).unwrap();
    }
}

#[test]
fn streamed_transitivity_still_rejects_disconnected_or_redundant_edges() {
    let mut f = array_chain();
    let disconnected = eq(&mut f.terms, f.left, f.right);
    let first = [f.first];
    let second = [f.second];
    let disconnected = [disconnected];
    for premises in [
        vec![&first[..], &disconnected[..]],
        vec![&first[..], &second[..], &first[..]],
    ] {
        assert!(!trans_step_surface_is_supported(
            &f.terms,
            &[f.goal],
            &premises,
            None
        ));
    }
    let overrides = [(f.first, "(= middle right)".to_string())]
        .into_iter()
        .collect();
    assert!(!trans_step_surface_is_supported(
        &f.terms,
        &[f.goal],
        &[&[f.first], &[f.second]],
        Some(&overrides),
    ));
}

#[test]
fn streaming_preserves_special_application_spellings() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("a b", Sort::bitvec(8));
    let tester = terms.mk_app(Symbol::named("is-Thing"), vec![x], Sort::Bool);
    let extract = terms.mk_app(
        Symbol::indexed("extract", vec![3, 0]),
        vec![x],
        Sort::bitvec(4),
    );
    let clause = terms.mk_app(Symbol::named("cl"), Vec::new(), Sort::Bool);
    let user_clause = terms.mk_var("cl", Sort::Bool);
    let zero = terms.mk_bitvec(BigInt::from(0), 8);
    let constant_array = terms.mk_app(
        Symbol::named("const-array"),
        vec![zero],
        Sort::array(Sort::bitvec(64), Sort::bitvec(8)),
    );
    let printer = AlethePrinter::new(&terms);
    assert_eq!(printer.format_term(tester), "((_ is Thing) |a b|)");
    assert_eq!(printer.format_term(extract), "((_ extract 3 0) |a b|)");
    assert_eq!(printer.format_term(clause), "(cl)");
    assert_eq!(printer.format_term(user_clause), "|cl|");
    assert_eq!(
        printer.format_term(constant_array),
        "((as const (Array (_ BitVec 64) (_ BitVec 8))) #b00000000)"
    );
}

#[test]
fn streaming_preserves_all_effective_rendering_channels() {
    let f = array_chain();
    let overrides = [(f.middle, "authored_middle".to_string())]
        .into_iter()
        .collect();
    let printer = AlethePrinter::new_with_overrides(&f.terms, Some(&overrides));
    printer
        .let_bridge_renderings
        .borrow_mut()
        .insert(f.right, "let_right".to_string());
    printer
        .skolem_overrides
        .borrow_mut()
        .insert(f.left, "skolem_left".to_string());
    assert_eq!(
        printer.format_term(f.first),
        "(= skolem_left authored_middle)"
    );
    assert_eq!(
        printer.format_term(f.second),
        "(= authored_middle let_right)"
    );
    let effective = printer.judgement_overrides();
    assert!(trans_step_surface_is_supported(
        &f.terms,
        &[f.goal],
        &[&[f.first], &[f.second]],
        effective.as_ref(),
    ));
}

#[test]
fn streaming_does_not_hide_expanded_output_exhaustion() {
    let mut terms = TermStore::new();
    let mut root = terms.mk_var("x", Sort::bitvec(8));
    for _ in 0..24 {
        root = terms.mk_app(Symbol::named("bvadd"), vec![root, root], Sort::bitvec(8));
    }
    let printer = AlethePrinter::new_with_overrides_and_budget(&terms, None, Some(1024));
    let text = printer.format_term(root);
    assert!(printer.work_budget_exhausted());
    assert!(
        text.len() < 2048,
        "do not expand the exponential DAG after refusal"
    );
    assert!(printer.check_emission_progress(0).is_err());
}

#[test]
fn bounded_channel_copy_refuses_override_skolem_bridge_and_cache_before_copying() {
    let mut terms = TermStore::new();
    let variable = terms.mk_var("x", Sort::Int);
    let huge = "oversized_payload".repeat(65_536);
    for channel in 0..4 {
        let overrides = HashMap::from_iter([(variable, huge.clone())]);
        let printer = AlethePrinter::new_with_overrides_and_budget(
            &terms,
            (channel == 0).then_some(&overrides),
            Some(64),
        );
        match channel {
            1 => {
                printer
                    .skolem_overrides
                    .borrow_mut()
                    .insert(variable, huge.clone());
            }
            2 => {
                printer
                    .let_bridge_renderings
                    .borrow_mut()
                    .insert(variable, huge.clone());
            }
            3 => {
                printer
                    .format_cache
                    .borrow_mut()
                    .insert(variable, huge.clone());
            }
            _ => {}
        }
        let text = printer.format_term(variable);
        assert!(printer.work_budget_exhausted());
        assert!(
            text.len() < 64 && text.capacity() < 128,
            "channel {channel} copied oversized bytes"
        );
        assert!(!text.contains("oversized_payload"));
    }
}

#[test]
fn bounded_derived_negation_does_not_clone_an_oversized_inner_bridge() {
    let mut terms = TermStore::new();
    let predicate = terms.mk_var("p", Sort::Bool);
    let negation = terms.mk_not_raw(predicate);
    let printer = AlethePrinter::new_with_overrides_and_budget(&terms, None, Some(64));
    printer
        .let_bridge_renderings
        .borrow_mut()
        .insert(predicate, "large".repeat(200_000));
    let text = printer.format_derived_literal(negation);
    assert!(printer.work_budget_exhausted());
    assert!(text.len() < 64 && text.capacity() < 128);
    assert!(!text.contains("large"));
}

#[test]
fn explicit_unbounded_rendering_keeps_the_requested_channel_bytes() {
    let mut terms = TermStore::new();
    let variable = terms.mk_var("x", Sort::Int);
    let huge = "unbounded_payload".repeat(8_192);
    let overrides = HashMap::from_iter([(variable, huge.clone())]);
    let printer = AlethePrinter::new_with_overrides(&terms, Some(&overrides));
    assert_eq!(printer.format_term(variable), huge);
    assert!(!printer.work_budget_exhausted());
}

#[test]
fn bounded_channel_copy_polls_without_a_borrow_and_rejects_changed_admission() {
    let mut terms = TermStore::new();
    let variable = terms.mk_var("x", Sort::Int);
    let channel = std::cell::RefCell::new(HashMap::from_iter([(variable, "small".into())]));
    let mut changed = false;
    let mut progress = || {
        if !changed {
            channel
                .borrow_mut()
                .insert(variable, "late_large".repeat(100_000));
            changed = true;
        }
        true
    };
    let printer = AlethePrinter::new_with_overrides_and_budget(&terms, None, Some(u64::MAX))
        .with_emission_progress(&mut progress);
    let mut out = String::new();
    assert!(printer.write_rendering_channel_into(&mut out, variable, &channel, "", ""));
    assert!(printer.work_budget_exhausted());
    assert!(out.len() < 64 && out.capacity() < 128);
}

#[test]
fn bounded_channel_copy_preserves_caller_cancellation_before_copy() {
    let mut terms = TermStore::new();
    let variable = terms.mk_var("x", Sort::Int);
    let channel = std::cell::RefCell::new(HashMap::from_iter([(variable, "not_emitted".into())]));
    let mut progress = || false;
    let printer = AlethePrinter::new_with_overrides_and_budget(&terms, None, Some(1024))
        .with_emission_progress(&mut progress);
    let mut out = String::new();
    assert!(printer.write_rendering_channel_into(&mut out, variable, &channel, "", ""));
    assert!(printer.emission_progress.refused());
    assert!(!out.contains("not_emitted"));
}
