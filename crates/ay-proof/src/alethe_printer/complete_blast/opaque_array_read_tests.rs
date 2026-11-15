// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::super::opaque_array_read::ReadChildren;
use super::*;
use ay_core::{Proof, TheoryLemmaKind};

fn read(f: &mut Fixture, name: &str) -> (TermId, TermId, TermId) {
    let memory = f
        .terms
        .mk_var(name, Sort::array(Sort::bitvec(4), Sort::bitvec(4)));
    let index = f.bv("index", 4);
    let value = f.op("select", &[memory, index], 4);
    (memory, index, value)
}

fn quotient_remainder(f: &mut Fixture, value: TermId) -> TermId {
    let divisor = f.bv("divisor", 4);
    let quotient = f.op("bvudiv", &[value, divisor], 4);
    let product = f.op("bvmul", &[quotient, divisor], 4);
    let remainder = f.op("bvurem", &[value, divisor], 4);
    let sum = f.op("bvadd", &[product, remainder], 4);
    f.equals(value, sum)
}

fn capture(problem: &str, proof: &str) {
    use std::io::Write;
    let Some(path) = std::env::var_os("AY_COMPLETE_BLAST_ARTIFACT_DIR") else {
        return;
    };
    let path = std::path::PathBuf::from(path);
    assert!(path.is_absolute());
    std::fs::create_dir_all(&path).unwrap();
    let certificate=serde_json::to_vec(&serde_json::json!({"type":"alethe_certificate","version":"1.0","problem":problem,"proof":proof})).unwrap();
    assert!(certificate.len() <= 16 * 1024 * 1024);
    for (name, bytes) in [
        ("original.smt2", problem.as_bytes()),
        ("proof.alethe", proof.as_bytes()),
        ("certificate.json", certificate.as_slice()),
    ] {
        let mut file = std::fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(path.join(name))
            .unwrap();
        file.write_all(bytes).unwrap();
    }
}

#[test]
fn actual_array_read_is_an_opaque_word_in_a_checked_complete_refutation() {
    let mut f = Fixture::new();
    let (_, _, value) = read(&mut f, "memory");
    let lemma = quotient_remainder(&mut f, value);
    let assertion = f.not(lemma);
    let mut proof = Proof::new();
    let premise = proof.add_assume(assertion, None);
    let theorem = proof.add_theory_lemma_with_kind("bv", vec![lemma], TheoryLemmaKind::BvBitBlast);
    proof.add_resolution(vec![], assertion, premise, theorem);
    crate::check_proof_strict_with_context(&proof, &f.terms, None, None, Some(&[assertion]))
        .unwrap();
    let document = crate::try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &f.terms,
        &[assertion],
        None,
    )
    .unwrap();
    assert_complete(&document);
    assert!(
        document.contains("@ay_cbb_"),
        "must enter complete-blast rather than another named identity lane"
    );
    assert!(document.contains("(select memory index)"));
    assert!(document.contains(":rule bitblast_var"));
    let problem = format!("(set-logic QF_ABV)\n(declare-const memory (Array (_ BitVec 4) (_ BitVec 4)))\n(declare-const index (_ BitVec 4))\n(declare-const divisor (_ BitVec 4))\n(assert {})\n(check-sat)\n",crate::format_term_alethe(&f.terms,assertion));
    capture(&problem, &document);
}

#[test]
fn distinct_read_indices_gain_no_unproved_array_relationship() {
    let mut f = Fixture::new();
    let (memory, _, first) = read(&mut f, "memory");
    let other_index = f.bv("other_index", 4);
    let second = f.op("select", &[memory, other_index], 4);
    let equality = f.equals(first, second);
    assert!(AlethePrinter::new(&f.terms)
        .format_bv_complete_blast_refutation(ProofId(1), &[equality])
        .is_none());
}

#[test]
fn array_leaf_and_index_keep_exact_sorts_and_live_arena_checks() {
    for malformed in 0..3 {
        let mut f = Fixture::new();
        let (memory, index, _) = read(&mut f, "memory");
        let index = if malformed == 0 {
            f.bv("wrong_width", 3)
        } else {
            index
        };
        let array = if malformed == 1 {
            TermId(u32::MAX)
        } else {
            memory
        };
        let width = if malformed == 2 { 3 } else { 4 };
        let value = f.op("select", &[array, index], width);
        let printer = AlethePrinter::new(&f.terms);
        let mut blaster = Blaster::new(&printer, ProofId(1), "@read_sort_".into());
        assert!(matches!(
            blaster.opaque_array_variable_read(value),
            ReadChildren::Refused
        ));
    }
}

#[test]
fn array_variable_surface_override_and_anchor_scope_are_not_hidden_by_abstraction() {
    let mut f = Fixture::new();
    let (memory, _, value) = read(&mut f, "memory");
    let overrides = [(memory, "other_memory".to_string())].into_iter().collect();
    let printer = AlethePrinter::new_with_overrides_and_budget(&f.terms, Some(&overrides), None);
    let mut blaster = Blaster::new(&printer, ProofId(1), "@read_surface_".into());
    assert!(matches!(
        blaster.opaque_array_variable_read(value),
        ReadChildren::Refused
    ));
    let printer = AlethePrinter::new(&f.terms);
    printer
        .anchor_binder_names
        .borrow_mut()
        .insert("memory".into());
    let mut blaster = Blaster::new(&printer, ProofId(1), "@read_anchor_".into());
    assert!(matches!(
        blaster.opaque_array_variable_read(value),
        ReadChildren::Refused
    ));
}

#[test]
fn unique_array_leaf_counts_against_the_same_exact_source_node_boundary() {
    let mut f = Fixture::new();
    let (_, _, value) = read(&mut f, "memory");
    let root = f.equals(value, value);
    for room in [3usize, 4] {
        let printer = AlethePrinter::new(&f.terms);
        let mut blaster = Blaster::new(&printer, ProofId(1), "@read_nodes_".into());
        blaster.walked = MAX_TERM_NODES - room;
        assert_eq!(blaster.prepare(root).is_some(), room == 4);
        assert_eq!(blaster.opaque_array_variables.len(), 1);
    }
    let printer = AlethePrinter::new(&f.terms);
    let mut blaster = Blaster::new(&printer, ProofId(1), "@read_full_".into());
    blaster.walked = MAX_TERM_NODES;
    assert!(matches!(
        blaster.opaque_array_variable_read(value),
        ReadChildren::Refused
    ));
    assert!(blaster.opaque_array_variables.is_empty());
    assert_eq!(blaster.walked, MAX_TERM_NODES);
}

#[test]
fn new_array_leaf_still_obeys_live_stop_and_render_work_budget() {
    let mut f = Fixture::new();
    let (_, _, value) = read(&mut f, &"memory".repeat(4096));
    let lemma = quotient_remainder(&mut f, value);
    assert!(
        AlethePrinter::new_with_overrides_and_budget(&f.terms, None, Some(128))
            .format_bv_complete_blast_refutation(ProofId(1), &[lemma])
            .is_none()
    );
    let stopped = || true;
    assert!(AlethePrinter::new(&f.terms)
        .asking_complete_blast(CompleteBlastAsk::AskedUntil(&stopped))
        .format_bv_complete_blast_refutation(ProofId(1), &[lemma])
        .is_none());
}
