// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::{
    decode_printed_literal, normalise_printed_spelling, OwnedText, PrintedClause, TextBudget,
    WireLiteral, WireParts, COUNTER_BYTES, MAX_NORMALISED_DEPTH, MAX_RECORDED_PRINTED_BYTES,
};
use crate::alethe_printer::AlethePrinter;
use ay_core::{Proof, ProofId, TermStore};
use std::hash::{BuildHasherDefault, Hasher};

#[test]
fn wire_storage_roundtrips_exact_shells_and_opaque_syntax() {
    let samples = [
        "p",
        "(not p)",
        "(not (not p))",
        "(not  p)",
        "(not p )",
        "(|not| p)",
        "(not)",
        "(not )",
        "(not p q)",
        "(not (p)",
        "(not ())",
        "(not |λ (x)\\| y|)",
        "(not \"a)\"\"b\")",
        "(not λ)",
        "(not\tλ)",
        "(not |not|)",
    ];
    let terms = TermStore::new();
    let printer = AlethePrinter::new(&terms);
    for text in samples {
        let ids = printer.record_interned_clause(&[text]).unwrap();
        let wire = printer.printed_wire_literals(&ids).unwrap();
        let exact = printer.printed_atom_texts(&ids).unwrap();
        assert_eq!(exact[0].as_ref(), text);
        let parts = WireParts::read(text);
        assert_eq!(wire[0].shells, parts.shells);
        if let Some((atom, depth)) = decode_printed_literal(text) {
            let mut nodes = 0;
            let expected = normalise_printed_spelling(&atom, 0, &mut nodes);
            let decoded = printer.printed_wire_identity(&wire[0]).unwrap();
            assert_eq!(decoded.depth, depth, "{text}");
            assert_eq!(decoded.atom.as_ref(), atom);
            assert_eq!(decoded.spelling.as_ref(), expected);
        }
    }
    assert_eq!(WireParts::read("(not (not p))").shells, 2);
    for text in [
        "(not)",
        "(not )",
        "(not p q)",
        "(not (p)",
        "(not ())",
        "(not  p)",
        "(not p )",
        "(|not| p)",
    ] {
        assert_eq!(WireParts::read(text).shells, 0, "{text}");
    }
}

#[test]
fn wire_storage_distinguishes_actual_bytes_even_when_normalization_agrees() {
    let terms = TermStore::new();
    let printer = AlethePrinter::new(&terms);
    let ids = printer
        .record_interned_clause(&["(= x #b0000)", "(= x (_ bv0 4))"])
        .unwrap();
    assert_ne!(ids[0], ids[1]);
    let wires = printer.printed_wire_literals(&ids).unwrap();
    assert_ne!(wires[0].body, wires[1].body);
    let left = printer.printed_wire_identity(&wires[0]).unwrap();
    let right = printer.printed_wire_identity(&wires[1]).unwrap();
    assert_eq!(left.spelling, right.spelling);
}

#[derive(Default)]
struct Collision;
impl Hasher for Collision {
    fn finish(&self) -> u64 {
        0
    }
    fn write(&mut self, _: &[u8]) {}
}
#[test]
fn wire_storage_hash_collisions_never_merge_different_raw_bodies_or_shells() {
    let budget = TextBudget::new(MAX_RECORDED_PRINTED_BYTES);
    let a = budget.copy("a").unwrap();
    let b = budget.copy("b").unwrap();
    #[expect(
        clippy::mutable_key_type,
        reason = "the test exercises OwnedText's immutable text identity despite its accounting Cell"
    )]
    let mut bodies =
        std::collections::HashMap::<OwnedText, usize, BuildHasherDefault<Collision>>::default();
    bodies.insert(a.clone(), 1);
    bodies.insert(b.clone(), 2);
    assert_eq!(bodies.get("a"), Some(&1));
    assert_eq!(bodies.get("b"), Some(&2));
    #[expect(
        clippy::mutable_key_type,
        reason = "the test exercises WireLiteral's immutable text identity despite its accounting Cell"
    )]
    let mut literals =
        std::collections::HashMap::<WireLiteral, usize, BuildHasherDefault<Collision>>::default();
    for (i, key) in [
        WireLiteral {
            body: a.clone(),
            shells: 0,
        },
        WireLiteral { body: a, shells: 2 },
        WireLiteral { body: b, shells: 0 },
    ]
    .into_iter()
    .enumerate()
    {
        literals.insert(key, i);
    }
    assert_eq!(literals.len(), 3);
}

#[test]
fn wire_storage_shares_large_opposite_spellings_without_changing_rup() {
    let terms = TermStore::new();
    let printer = AlethePrinter::new(&terms);
    let a = "a".repeat(2_600_000);
    let b = "b";
    let equality = format!("(= {a} {b})");
    let source = printer
        .record_interned_clause(std::slice::from_ref(&a))
        .unwrap();
    let eq = printer
        .record_interned_clause(std::slice::from_ref(&equality))
        .unwrap();
    let before = printer.printed_clause_bytes.get();
    let implication = printer
        .record_interned_clause(&[format!("(not {equality})"), format!("(not {a})"), b.into()])
        .unwrap();
    assert!(printer.printed_clause_bytes.get() - before < 4096);
    assert!(printer.printed_clause_bytes.get() < MAX_RECORDED_PRINTED_BYTES);
    let views = vec![
        printer.printed_wire_literals(&source).unwrap(),
        printer.printed_wire_literals(&eq).unwrap(),
        printer.printed_wire_literals(&implication).unwrap(),
    ];
    let decoded = printer.decode_wire_all(&views).unwrap();
    let goal = printer.printed_literal_identity(b).unwrap();
    assert_eq!(printer.printed_rup_entail(&decoded, &[goal]), Some(true));
    let wrong = printer.printed_literal_identity("c").unwrap();
    assert_eq!(printer.printed_rup_entail(&decoded, &[wrong]), Some(false));
}

#[test]
fn wire_storage_external_handles_keep_allocation_charged_across_reset() {
    let terms = TermStore::new();
    let printer = AlethePrinter::new(&terms);
    let text = "x".repeat(4096);
    let ids = printer
        .record_interned_clause(std::slice::from_ref(&text))
        .unwrap();
    let held = printer.printed_wire_literals(&ids).unwrap();
    printer.release_printed_atoms(ids);
    printer.prepare_proof(&Proof::from_steps(vec![])).unwrap();
    assert_eq!(held[0].body.as_ref(), text);
    assert_eq!(
        printer.printed_clause_bytes.get(),
        COUNTER_BYTES + OwnedText::cost(text.len()).unwrap()
    );
    drop(held);
    assert_eq!(printer.printed_clause_bytes.get(), COUNTER_BYTES);
}

#[test]
fn wire_storage_unshared_text_and_stale_generations_keep_refusing() {
    let terms = TermStore::new();
    let printer = AlethePrinter::new(&terms);
    let before = printer.printed_clause_bytes.get();
    assert!(printer
        .record_interned_clause(&["x".repeat(MAX_RECORDED_PRINTED_BYTES)])
        .is_none());
    assert_eq!(printer.printed_clause_bytes.get(), before);
    assert!(printer.printed_clause_atom_index.borrow().is_empty());
    let first = printer.record_interned_clause(&["x"]).unwrap();
    let stale = first[0];
    printer.release_printed_atoms(first);
    let next = printer.record_interned_clause(&["y"]).unwrap();
    assert_ne!(stale, next[0]);
    assert!(printer.printed_wire_literals(&[stale]).is_none());
}

#[test]
fn wire_storage_scratch_refusal_cannot_approve_unreadable_resolution() {
    let mut terms = TermStore::new();
    let p = terms.mk_bool(true);
    let printer = AlethePrinter::new(&terms);
    printer.printed_clause_ledger_active.set(true);
    let ids = printer.record_interned_clause(&["p"]).unwrap();
    printer
        .printed_step_clauses
        .borrow_mut()
        .insert(ProofId(0), PrintedClause::Literals(ids));
    *printer.printed_replay_scratch.borrow_mut() = Some(TextBudget::new(COUNTER_BYTES));
    let result = printer
        .judge_printed_resolution(ProofId(1), &[p], "(cl p)", &[ProofId(0)])
        .unwrap();
    assert!(result.is_some_and(|text| text.contains(ay_core::UNPROVED_STEP_RULE)));
}

#[test]
fn wire_storage_deep_shells_and_wide_literals_keep_the_complete_legacy_reading() {
    let terms = TermStore::new();
    let printer = AlethePrinter::new(&terms);
    let mut deep = "λ".to_owned();
    for _ in 0..70 {
        deep = format!("(not {deep})");
    }
    let ids = printer.record_interned_clause(&[deep.clone()]).unwrap();
    let wire = printer.printed_wire_literals(&ids).unwrap();
    assert_eq!(wire[0].shells, MAX_NORMALISED_DEPTH);
    assert_eq!(printer.printed_atom_texts(&ids).unwrap()[0].as_ref(), deep);
    assert_eq!(printer.printed_wire_identity(&wire[0]).unwrap().depth, 70);
    let wide = format!("(= #b{} (_ bv1 4096))", "1".repeat(4096));
    let mut old_nodes = 0;
    let expected = normalise_printed_spelling(&wide, 0, &mut old_nodes);
    let actual = printer.printed_literal_identity(&wide).unwrap();
    assert_eq!(actual.spelling.as_ref(), expected);
}

#[test]
fn wire_storage_counts_simultaneously_live_text_and_vector_capacities() {
    let budget = TextBudget::new(1024);
    let baseline = budget.used.get();
    let first = budget.copy(&"x".repeat(400)).unwrap();
    let held = first.clone();
    let allocated = budget.used.get();
    drop(first);
    assert_eq!(budget.used.get(), allocated);
    let vector = budget.vector::<u64>(40).unwrap();
    assert_eq!(
        budget.used.get(),
        allocated + vector.capacity() * size_of::<u64>()
    );
    assert!(budget.copy(&"y".repeat(300)).is_none());
    drop(vector);
    assert_eq!(budget.used.get(), allocated);
    drop(held);
    assert_eq!(budget.used.get(), baseline);
}

#[test]
fn wire_storage_live_stop_cannot_reuse_a_memo_or_mutate_retained_state() {
    use std::cell::Cell;
    let running = Cell::new(true);
    let mut poll = || running.get();
    let terms = TermStore::new();
    let printer = AlethePrinter::new(&terms).with_emission_progress(&mut poll);
    let ids = printer.record_interned_clause(&["(not p)"]).unwrap();
    let wire = printer.printed_wire_literals(&ids).unwrap();
    printer.printed_wire_identity(&wire[0]).unwrap();
    let before = printer.printed_clause_bytes.get();
    let slots = printer.printed_clause_atom_texts.borrow().len();
    running.set(false);
    assert!(printer.printed_wire_identity(&wire[0]).is_none());
    assert!(printer.record_interned_clause(&["new"]).is_none());
    assert_eq!(printer.printed_clause_bytes.get(), before);
    assert_eq!(printer.printed_clause_atom_texts.borrow().len(), slots);
}

#[test]
fn wire_storage_accounting_underflow_poison_survives_scope_exit_and_reset() {
    use super::wire_text::ScratchScope;
    let terms = TermStore::new();
    let printer = AlethePrinter::new(&terms);
    let held = {
        let _scope = ScratchScope::enter(
            &printer.printed_replay_scratch,
            super::super::printed_command::MAX_STEP_BYTES,
            &printer.printed_clause_bytes,
        );
        let budget = printer.printed_replay_budget();
        let held = budget.copy("live escaped allocation").unwrap();
        // Simulate an accounting invariant failure after the outer scope
        // closes; the surviving owner must poison its printer parent too.
        budget.used.set(0);
        held
    };
    assert!(!printer.printed_clause_bytes.is_poisoned());
    drop(held);
    assert!(printer.printed_clause_bytes.is_poisoned());
    assert!(printer.check_emission_progress(0).is_err());
    assert!(printer.record_interned_clause(&["p"]).is_none());
    printer.plan_printed_clause_demand(&Proof::from_steps(vec![]));
    assert!(printer.printed_clause_bytes.is_poisoned());
    assert!(printer.prepare_proof(&Proof::from_steps(vec![])).is_err());
    let budget = TextBudget::retained(
        printer.printed_clause_bytes.clone(),
        MAX_RECORDED_PRINTED_BYTES,
    );
    assert!(budget.copy("p").is_none());
}

#[test]
fn wire_storage_resize_underflow_is_sticky_even_if_counter_is_reset() {
    let budget = TextBudget::new(4096);
    let mut lease = budget.reserve(128).unwrap();
    budget.used.set(0);
    assert!(lease.resize(64, 4096).is_none());
    assert!(budget.used.is_poisoned());
    budget.used.set(COUNTER_BYTES);
    assert!(budget.reserve(1).is_none());
}
