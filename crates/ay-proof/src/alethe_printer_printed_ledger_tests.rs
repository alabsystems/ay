// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Lifetime and ownership controls for the actual printed-clause ledger.
use super::super::AlethePrinter;
use super::{
    atom_id, rc_text_bytes, PrintedClause, ATOM_SLOT_MASK, MAX_ATOM_GENERATION,
    MAX_RECORDED_PRINTED_BYTES,
};
use ay_core::{AletheRule, Proof, ProofId, ProofStep, TermStore};

fn step(rule: AletheRule, premises: &[u32]) -> ProofStep {
    ProofStep::Step {
        rule,
        clause: vec![],
        premises: premises.iter().copied().map(ProofId).collect(),
        args: vec![],
    }
}

#[test]
fn retirement_waits_for_all_native_edges_and_pins_assumptions() {
    let mut terms = TermStore::new();
    let p = terms.mk_bool(true);
    let proof = Proof::from_steps(vec![
        ProofStep::Assume(p),
        step(AletheRule::Refl, &[]),
        step(AletheRule::Resolution, &[0, 1]),
        ProofStep::Anchor {
            end_step: ProofId(5),
            variables: vec![],
        },
        // This consumer does not consult the ledger today. Still retain
        // t1 through it, so synthetic helpers cannot outlive their input.
        step(AletheRule::Reordering, &[1]),
        step(AletheRule::Resolution, &[0, 2]),
    ]);
    let printer = AlethePrinter::new(&terms);
    printer.prepare_proof(&proof).unwrap();
    for id in [0, 1, 2] {
        printer.record_printed_conclusion(ProofId(id), &format!("(step t{id} (cl p) :rule refl)"));
    }
    printer.finish_exported_step(ProofId(2));
    assert!(printer
        .printed_step_clauses
        .borrow()
        .contains_key(&ProofId(1)));
    printer.finish_exported_step(ProofId(3));
    assert!(printer
        .printed_step_clauses
        .borrow()
        .contains_key(&ProofId(1)));
    printer.finish_exported_step(ProofId(4));
    assert!(!printer
        .printed_step_clauses
        .borrow()
        .contains_key(&ProofId(1)));
    assert!(printer
        .printed_step_clauses
        .borrow()
        .contains_key(&ProofId(2)));
    printer.finish_exported_step(ProofId(5));
    assert!(!printer
        .printed_step_clauses
        .borrow()
        .contains_key(&ProofId(2)));
    assert!(printer
        .printed_step_clauses
        .borrow()
        .contains_key(&ProofId(0)));
}

#[test]
fn retirement_frees_only_last_owned_text_and_keeps_metadata_charged() {
    let terms = TermStore::new();
    let printer = AlethePrinter::new(&terms);
    let atom = "a".repeat(1024);
    let first = printer
        .record_interned_clause(&[atom.clone(), atom.clone()])
        .unwrap();
    let second = printer.record_interned_clause(&[atom.clone()]).unwrap();
    let initial = printer.printed_clause_bytes.get();
    printer.release_printed_atoms(first);
    assert_eq!(
        printer.printed_clause_bytes.get(),
        initial - 2 * std::mem::size_of::<u32>()
    );
    assert!(printer.printed_atom_texts(&second).is_some());
    let stale = second[0];
    printer.release_printed_atoms(second);
    assert_eq!(
        printer.printed_clause_bytes.get(),
        initial - 3 * std::mem::size_of::<u32>() - super::OwnedText::cost(atom.len()).unwrap()
    );
    assert!(
        printer.printed_clause_bytes.get() > 0,
        "allocated index and slot capacity still exists"
    );
    assert_eq!(printer.printed_clause_atom_texts.borrow().len(), 1);
    assert!(printer.printed_clause_atom_index.borrow().is_empty());
    assert!(printer.printed_atom_texts(&[stale]).is_none());
    let replacement = printer
        .record_interned_clause(&["replacement".to_owned()])
        .unwrap();
    assert_eq!(stale & ATOM_SLOT_MASK, replacement[0] & ATOM_SLOT_MASK);
    assert_ne!(stale, replacement[0]);
    assert!(printer.printed_atom_texts(&[stale]).is_none());
    assert_eq!(
        &*printer.printed_atom_texts(&replacement).unwrap()[0],
        "replacement"
    );
}

#[test]
fn external_text_owners_prevent_refunds_and_generation_wrap_never_aliases() {
    let terms = TermStore::new();
    let printer = AlethePrinter::new(&terms);
    let ids = printer
        .record_interned_clause(&["owned".to_owned()])
        .unwrap();
    let borrowed = printer.printed_atom_texts(&ids).unwrap();
    let before = printer.printed_clause_bytes.get();
    printer.release_printed_atoms(ids);
    assert_eq!(
        printer.printed_clause_bytes.get(),
        before - std::mem::size_of::<u32>()
    );
    assert!(printer.printed_clause_atom_index.borrow().is_empty());
    let held = printer.printed_clause_bytes.get();
    drop(borrowed);
    assert_eq!(
        printer.printed_clause_bytes.get(),
        held - super::OwnedText::cost("owned".len()).unwrap()
    );
    let mut ids = printer
        .record_interned_clause(&["owned".to_owned()])
        .unwrap();
    let slot = (ids[0] & ATOM_SLOT_MASK) as usize;
    // Exercise the terminal generation without cycling sixteen thousand times.
    printer.printed_clause_atom_texts.borrow_mut()[slot].generation = MAX_ATOM_GENERATION;
    let terminal = atom_id(slot, MAX_ATOM_GENERATION);
    let key = printer.printed_clause_atom_texts.borrow()[slot]
        .text
        .clone()
        .unwrap();
    *printer
        .printed_clause_atom_index
        .borrow_mut()
        .get_mut(&key)
        .unwrap() = terminal;
    drop(key);
    ids[0] = terminal;
    printer.release_printed_atoms(ids);
    let replacement = printer.record_interned_clause(&["new".to_owned()]).unwrap();
    assert_ne!(terminal & ATOM_SLOT_MASK, replacement[0] & ATOM_SLOT_MASK);
    assert!(printer.printed_atom_texts(&[terminal]).is_none());
}

#[test]
fn disjoint_large_opposite_polarity_clauses_fit_without_a_lifetime_cap_increase() {
    let terms = TermStore::new();
    let printer = AlethePrinter::new(&terms);
    let mut cumulative = 0;
    for index in 0..12 {
        // Distinct complete wire literals. Neither a native TermId nor an
        // atom-only shortcut may merge the two polarities or successive pairs.
        let atom = format!("p{index}{}", "x".repeat(512 * 1024));
        let negative = format!("(not {atom})");
        cumulative += atom.len() + negative.len();
        let positive = printer.record_interned_clause(&[atom.clone()]).unwrap();
        let negative_ids = printer.record_interned_clause(&[negative.clone()]).unwrap();
        assert_ne!(positive[0], negative_ids[0]);
        let texts = vec![
            printer.printed_atom_texts(&positive).unwrap(),
            printer.printed_atom_texts(&negative_ids).unwrap(),
        ];
        let decoded = printer.decode_all(&texts).unwrap();
        assert_ne!(decoded[0][0].positive(), decoded[1][0].positive());
        assert_eq!(decoded[0][0].spelling, decoded[1][0].spelling);
        drop(texts);
        printer.release_printed_atoms(positive);
        printer.release_printed_atoms(negative_ids);
        assert!(printer.printed_clause_bytes.get() < 4096);
        assert!(printer.printed_literal_identity_bytes.get() <= MAX_RECORDED_PRINTED_BYTES);
    }
    assert!(cumulative > MAX_RECORDED_PRINTED_BYTES);
    assert_eq!(printer.printed_clause_atom_texts.borrow().len(), 2);
}

#[test]
fn refused_admission_preserves_slots_indices_and_refcounts() {
    let terms = TermStore::new();
    let printer = AlethePrinter::new(&terms);
    let ids = printer.record_interned_clause(&["p".to_owned()]).unwrap();
    printer.printed_clause_bytes.set(MAX_RECORDED_PRINTED_BYTES);
    let capacity = printer.printed_clause_atom_texts.borrow().capacity();
    let references = printer.printed_clause_atom_texts.borrow()[0].references;
    assert!(printer
        .record_interned_clause(&["p".to_owned(), "q".to_owned()])
        .is_none());
    assert_eq!(
        printer.printed_clause_bytes.get(),
        MAX_RECORDED_PRINTED_BYTES
    );
    assert_eq!(
        printer.printed_clause_atom_texts.borrow().capacity(),
        capacity
    );
    assert_eq!(
        printer.printed_clause_atom_texts.borrow()[0].references,
        references
    );
    assert_eq!(printer.printed_clause_atom_index.borrow().len(), 1);
    assert_eq!(&*printer.printed_atom_texts(&ids).unwrap()[0], "p");
}

#[test]
fn sequential_hook_preserves_unreadable_and_unbounded_refusals_until_last_use() {
    let terms = TermStore::new();
    let proof = Proof::from_steps(vec![
        step(AletheRule::Refl, &[]),
        step(AletheRule::Resolution, &[0]),
    ]);
    let printer = AlethePrinter::new(&terms);
    printer.prepare_proof(&proof).unwrap();
    printer.record_printed_conclusion(ProofId(0), "unreadable");
    assert_eq!(
        printer.printed_step_clauses.borrow().get(&ProofId(0)),
        Some(&PrintedClause::Unreadable)
    );
    printer.finish_exported_step(ProofId(0));
    assert!(printer
        .printed_step_clauses
        .borrow()
        .contains_key(&ProofId(0)));
    printer.printed_clause_bytes.set(MAX_RECORDED_PRINTED_BYTES);
    printer.record_printed_conclusion(ProofId(0), "(step t0 (cl p) :rule refl)");
    assert_eq!(
        printer.printed_step_clauses.borrow().get(&ProofId(0)),
        Some(&PrintedClause::Unbounded)
    );
    printer.finish_exported_step(ProofId(1));
    assert!(!printer
        .printed_step_clauses
        .borrow()
        .contains_key(&ProofId(0)));
}

#[test]
fn ordinary_export_retires_large_clauses_and_preserves_exact_refusal_controls() {
    use ay_core::{Sort, Symbol};
    use std::fmt::Write as _;
    let mut terms = TermStore::new();
    let mut proof = Proof::new();
    let mut assertions = Vec::new();
    let mut problem = String::from("(set-logic QF_UF)\n");
    let mut cumulative = 0;
    // Exact polarity sharing cuts the former fixture's retained text in
    // half. Sixty-four genuinely distinct bodies keep the ordinary no-GC
    // consumer beyond the same resident bound.
    for index in 0..64 {
        let name = format!("p{index}_{}", "x".repeat(48 * 1024));
        let atom = terms.mk_var(&name, Sort::Bool);
        let not_atom = terms.mk_not_raw(atom);
        let equality = terms.mk_app_structural(Symbol::Named("=".into()), [atom, atom], Sort::Bool);
        let not_equality = terms.mk_not_raw(equality);
        let tautology =
            terms.mk_app_structural(Symbol::Named("or".into()), [atom, not_atom], Sort::Bool);
        assertions.push(tautology);
        writeln!(
            problem,
            "(declare-const {name} Bool)\n(assert (or {name} (not {name})))"
        )
        .unwrap();
        let equality_id = proof.add_rule_step(AletheRule::Refl, vec![equality], vec![], vec![]);
        let axiom_id = proof.add_rule_step(
            AletheRule::EquivPos1,
            vec![not_equality, not_atom, atom],
            vec![],
            vec![],
        );
        proof.add_resolution(vec![not_atom, atom], equality, equality_id, axiom_id);
        cumulative += 6 * name.len();
    }
    assert!(cumulative / 2 > MAX_RECORDED_PRINTED_BYTES);
    let q = terms.mk_var("q", Sort::Bool);
    let not_q = terms.mk_not_raw(q);
    assertions.extend([q, not_q]);
    problem.push_str("(declare-const q Bool)\n(assert q)\n(assert (not q))\n(check-sat)\n");
    let positive = proof.add_assume(q, None);
    let negative = proof.add_assume(not_q, None);
    let final_id = proof.add_resolution(vec![], q, positive, negative);
    crate::check_proof_strict(&proof, &terms).expect("every native source step checks strictly");
    let exported = crate::try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &assertions,
        None,
    )
    .unwrap();
    assert!(!exported.contains(":rule hole"));
    assert!(exported.ends_with(&format!(
        "(step {final_id} (cl) :rule resolution :premises ({positive} {negative}))\n"
    )));

    // The same prepared printer without sequential completion retains the
    // entire cumulative ledger and must hit the unchanged bound honestly.
    let retained = AlethePrinter::new(&terms);
    retained.prepare_proof(&proof).unwrap();
    let mut refused = false;
    for (index, step) in proof.steps.iter().enumerate() {
        let text = retained.format_step(step, ProofId(index as u32)).unwrap();
        refused |= text.contains(":rule hole");
    }
    assert!(
        refused,
        "this case actually exceeds the previous lifetime retention"
    );

    if let Some(directory) = std::env::var_os("AY_PRINTED_LEDGER_ARTIFACT_DIR") {
        let directory = std::path::PathBuf::from(directory);
        std::fs::create_dir_all(&directory).unwrap();
        let missing = problem.replace("(assert (not q))\n", "");
        let wrong = exported.replace(
            &format!(":premises ({positive} {negative}))"),
            &format!(":premises ({positive} {positive}))"),
        );
        for (name, source, proof_text) in [
            ("positive", problem.as_str(), exported.as_str()),
            (
                "missing-source-premise",
                missing.as_str(),
                exported.as_str(),
            ),
            ("wrong-wire-premise", problem.as_str(), wrong.as_str()),
        ] {
            std::fs::write(directory.join(format!("{name}.smt2")), source).unwrap();
            std::fs::write(directory.join(format!("{name}.alethe")), proof_text).unwrap();
            let certificate = serde_json::json!({
                "type": "alethe_certificate", "version": "1.0", "problem": source, "proof": proof_text
            });
            std::fs::write(
                directory.join(format!("{name}.json")),
                serde_json::to_vec(&certificate).unwrap(),
            )
            .unwrap();
        }
    }
}

#[test]
fn oversized_retention_plan_leaves_an_active_fail_closed_ledger() {
    let terms = TermStore::new();
    let mut consumer = step(AletheRule::Resolution, &[]);
    if let ProofStep::Step { premises, .. } = &mut consumer {
        *premises = (0..(MAX_RECORDED_PRINTED_BYTES / 128 + 1) as u32)
            .map(ProofId)
            .collect();
    }
    let printer = AlethePrinter::new(&terms);
    printer.plan_printed_clause_demand(&Proof::from_steps(vec![consumer]));
    assert!(printer.printed_clause_ledger_active.get());
    assert!(printer.printed_clause_demand.borrow().is_empty());
    assert!(printer.printed_step_clauses.borrow().is_empty());
    assert_eq!(printer.printed_clause_bytes.get(), super::COUNTER_BYTES);
    assert!(printer
        .judge_printed_resolution(ProofId(1), &[], "(cl)", &[ProofId(0)])
        .unwrap()
        .unwrap()
        .contains(":rule hole"));
}
