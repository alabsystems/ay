// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::{AletheRule, Proof, TheoryLemmaKind};
use num_bigint::BigInt;

struct Fixture {
    terms: TermStore,
    root: TermId,
    read: TermId,
    value: TermId,
    keys: Vec<TermId>,
    guards: Vec<TermId>,
    equality: TermId,
    packed: TermId,
    assumption: TermId,
    declarations: String,
}

impl Fixture {
    fn new() -> Self {
        Self::variables(80)
    }

    fn variables(count: usize) -> Self {
        let mut terms = TermStore::new();
        let array = Sort::array(Sort::bitvec(64), Sort::bitvec(8));
        let mut root = terms.mk_var("memory", array.clone());
        let keys = (0..count)
            .map(|i| terms.mk_var(format!("i{i}"), Sort::bitvec(64)))
            .collect::<Vec<_>>();
        let value = terms.mk_bitvec(BigInt::from(7), 8);
        for (i, &key) in keys.iter().enumerate() {
            let stored = if i == 0 {
                value
            } else {
                terms.mk_bitvec(BigInt::from(i), 8)
            };
            root = terms.mk_app(
                Symbol::named("store"),
                vec![root, key, stored],
                array.clone(),
            );
        }
        let read = terms.mk_app(
            Symbol::named("select"),
            vec![root, keys[0]],
            Sort::bitvec(8),
        );
        let equality = terms.mk_app(Symbol::named("="), vec![read, value], Sort::Bool);
        let guards = keys[1..]
            .iter()
            .map(|&key| terms.mk_app(Symbol::named("="), vec![key, keys[0]], Sort::Bool))
            .collect::<Vec<_>>();
        let mut literals = guards.clone();
        literals.push(equality);
        let packed = terms.mk_app(Symbol::named("or"), literals, Sort::Bool);
        let assumption = terms.mk_not_raw(packed);
        let declarations = keys
            .iter()
            .enumerate()
            .map(|(i, _)| format!("(declare-const i{i} (_ BitVec 64))"))
            .collect::<Vec<_>>()
            .join("\n");
        Self {
            terms,
            root,
            read,
            value,
            keys,
            guards,
            equality,
            packed,
            assumption,
            declarations,
        }
    }

    fn frame_offsets() -> Self {
        let mut terms = TermStore::new();
        let array = Sort::array(Sort::bitvec(64), Sort::bitvec(8));
        let mut root = terms.mk_var("memory", array.clone());
        let sp = terms.mk_var("sp", Sort::bitvec(64));
        let words = (0..10)
            .map(|i| terms.mk_var(format!("saved{i}"), Sort::bitvec(64)))
            .collect::<Vec<_>>();
        let mut keys = Vec::new();
        let mut values = Vec::new();
        for i in 0..80 {
            let offset = terms.mk_bitvec(BigInt::from(i), 64);
            let key = terms.mk_app(Symbol::named("bvadd"), vec![sp, offset], Sort::bitvec(64));
            let low = (i % 8) * 8;
            let value = terms.mk_app(
                Symbol::indexed("extract", vec![low + 7, low]),
                vec![words[(i / 8) as usize]],
                Sort::bitvec(8),
            );
            keys.push(key);
            values.push(value);
            root = terms.mk_app(
                Symbol::named("store"),
                vec![root, key, value],
                array.clone(),
            );
        }
        let value = values[0];
        let read = terms.mk_app(
            Symbol::named("select"),
            vec![root, keys[0]],
            Sort::bitvec(8),
        );
        let equality = terms.mk_app(Symbol::named("="), vec![read, value], Sort::Bool);
        let guards = keys[1..]
            .iter()
            .map(|&key| terms.mk_app(Symbol::named("="), vec![key, keys[0]], Sort::Bool))
            .collect::<Vec<_>>();
        let mut literals = guards.clone();
        literals.push(equality);
        let packed = terms.mk_app(Symbol::named("or"), literals, Sort::Bool);
        let assumption = terms.mk_not_raw(packed);
        let declarations = format!(
            "(declare-const sp (_ BitVec 64))\n{}",
            (0..10)
                .map(|i| format!("(declare-const saved{i} (_ BitVec 64))"))
                .collect::<Vec<_>>()
                .join("\n")
        );
        Self {
            terms,
            root,
            read,
            value,
            keys,
            guards,
            equality,
            packed,
            assumption,
            declarations,
        }
    }

    fn retained_e1_prefix() -> Self {
        let source = include_str!("fixtures/e1_saved_store_prefix.smt2");
        let mut context = ay_frontend::Context::new();
        for command in ay_frontend::parse(source).unwrap() {
            context.process_command(&command).unwrap();
        }
        let mut terms = context.terms;
        let mut selected = None;
        for index in 0..terms.len() {
            let mut current = TermId(index as u32);
            let mut entries = Vec::new();
            while let TermData::App(Symbol::Named(op), args) = terms.get(current) {
                if op != "store" || args.len() != 3 {
                    break;
                }
                entries.push((args[1], args[2]));
                current = args[0];
            }
            if entries.len() == 80 {
                selected = Some((TermId(index as u32), entries));
                break;
            }
        }
        let (root, mut entries) =
            selected.expect("actual E1 saved store spine80 survives ordinary typed elaboration");
        entries.reverse();
        let keys = entries.iter().map(|e| e.0).collect::<Vec<_>>();
        let value = entries[0].1;
        let read = terms.mk_app(
            Symbol::named("select"),
            vec![root, keys[0]],
            Sort::bitvec(8),
        );
        let equality = terms.mk_app(Symbol::named("="), vec![read, value], Sort::Bool);
        let guards = keys[1..]
            .iter()
            .map(|&key| terms.mk_app(Symbol::named("="), vec![key, keys[0]], Sort::Bool))
            .collect::<Vec<_>>();
        let mut literals = guards.clone();
        literals.push(equality);
        let packed = terms.mk_app(Symbol::named("or"), literals, Sort::Bool);
        let assumption = terms.mk_not_raw(packed);
        let declarations = source
            .lines()
            .filter(|line| line.starts_with("(declare-"))
            .collect::<Vec<_>>()
            .join("\n");
        Self {
            terms,
            root,
            read,
            value,
            keys,
            guards,
            equality,
            packed,
            assumption,
            declarations,
        }
    }

    fn proof_unpacked(&mut self) -> Proof {
        let mut proof = Proof::new();
        let h = proof.add_assume(self.assumption, None);
        let mut literals = self.guards.clone();
        literals.push(self.equality);
        let lemma = proof.add_theory_lemma_with_kind(
            "array",
            literals.clone(),
            TheoryLemmaKind::ArrayRowChain,
        );
        let mut premises = vec![lemma];
        for (index, literal) in literals.into_iter().enumerate() {
            let negative = self.terms.mk_not_raw(literal);
            let argument = self.terms.mk_int(BigInt::from(index));
            premises.push(proof.add_rule_step(
                AletheRule::NotOr,
                vec![negative],
                vec![h],
                vec![argument],
            ));
        }
        proof.add_rule_step(AletheRule::Resolution, Vec::new(), premises, Vec::new());
        proof
    }

    fn proof(&self) -> Proof {
        let mut proof = Proof::new();
        let h = proof.add_assume(self.assumption, None);
        let lemma = proof.add_theory_lemma_with_kind(
            "array",
            vec![self.packed],
            TheoryLemmaKind::ArrayRowChain,
        );
        proof.add_resolution(Vec::new(), self.packed, lemma, h);
        proof
    }

    fn original(&self) -> String {
        let declarations = &self.declarations;
        format!("(set-logic QF_ABV)\n(declare-const memory (Array (_ BitVec 64) (_ BitVec 8)))\n{declarations}\n(assert {})\n(check-sat)\n",crate::format_term_alethe(&self.terms,self.assumption))
    }
}

fn capture(name: &str, problem: &str, proof: &str) {
    use std::io::Write;
    let Some(root) = std::env::var_os("AY_ROW_PREFIX_ARTIFACT_DIR") else {
        return;
    };
    let root = std::path::PathBuf::from(root);
    assert!(root.is_absolute());
    std::fs::create_dir_all(&root).unwrap();
    let certificate=serde_json::to_vec(&serde_json::json!({"type":"alethe_certificate","version":"1.0","problem":problem,"proof":proof})).unwrap();
    for (suffix, data) in [
        ("original.smt2", problem.as_bytes()),
        ("alethe", proof.as_bytes()),
        ("json", certificate.as_slice()),
    ] {
        let path = root.join(format!("{name}.{suffix}"));
        let mut file = std::fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(path)
            .unwrap();
        file.write_all(data).unwrap();
    }
}

#[test]
fn eighty_store_row_chain_keeps_raw_scope_and_emits_typed_shared_prefixes() {
    for (name, f) in [
        ("eighty-stores-79-guards", Fixture::new()),
        ("frame-offsets-and-byte-extracts", Fixture::frame_offsets()),
    ] {
        let proof = f.proof();
        crate::check_proof_strict(&proof, &f.terms).expect("unchanged native row-chain validator");
        let document = crate::try_export_alethe_with_problem_scope_and_overrides(
            &proof,
            &f.terms,
            &[f.assumption],
            None,
        )
        .expect("native production printer");
        assert_eq!(document.matches(":rule arrays_row").count(), 79);
        assert_eq!(document.matches("(define-fun @ay_row_").count(), 80);
        assert!(document.contains(":rule arrays_idx") && document.contains("t1.pread"));
        assert!(!document.contains(":rule hole") && !document.contains(":rule trust"));
        assert!(document.contains(&format!(
            "(assume t0 {})",
            crate::format_term_alethe(&f.terms, f.assumption)
        )));
        assert!(document.len() < 2 * 1024 * 1024);
        capture(name, &f.original(), &document);

        // Same original, but the candidate definition no longer states the store
        // the ROW chain needs. Independent replay must refuse this document.
        let definition = document
            .lines()
            .find(|line| line.starts_with("(define-fun @ay_row_"))
            .unwrap();
        let fields =
            split_alethe_application_bounded(definition, "define-fun", 4, MAX_RAW_BYTES).unwrap();
        let store = split_alethe_application_bounded(fields[3], "store", 3, MAX_RAW_BYTES).unwrap();
        let changed = format!(
            "(define-fun {} () {} (store {} {} #b11111111))",
            fields[0], fields[2], store[0], store[1]
        );
        let altered = document.replacen(definition, &changed, 1);
        assert_ne!(altered, document);
        capture(
            &format!("{name}-wrong-definition-value"),
            &f.original(),
            &altered,
        );
        let altered = document.replacen(
            "(Array (_ BitVec 64) (_ BitVec 8))",
            "(Array (_ BitVec 64) (_ BitVec 16))",
            1,
        );
        assert_ne!(altered, document);
        capture(
            &format!("{name}-wrong-definition-sort"),
            &f.original(),
            &altered,
        );
        let definitions = document
            .lines()
            .filter(|line| line.starts_with("(define-fun @ay_row_"))
            .collect::<Vec<_>>();
        let pair = format!("{}\n{}", definitions[0], definitions[1]);
        let reversed = format!("{}\n{}", definitions[1], definitions[0]);
        let altered = document.replacen(&pair, &reversed, 1);
        assert_ne!(altered, document);
        capture(
            &format!("{name}-forward-reference"),
            &f.original(),
            &altered,
        );
        let guard = document
            .lines()
            .find(|line| line.starts_with("(assume t1.h0 "))
            .unwrap();
        let index = crate::format_term_alethe(&f.terms, f.keys[0]);
        let changed = format!("(assume t1.h0 (not (= {index} {index})))");
        let altered = document.replacen(guard, &changed, 1);
        assert_ne!(altered, document);
        capture(&format!("{name}-wrong-guard"), &f.original(), &altered);
    }
}

#[test]
fn raw_overrides_and_anchor_binders_never_acquire_shared_definitions() {
    let f = Fixture::new();
    let rendered = crate::format_term_alethe(&f.terms, f.root);
    let exact: HashMap<_, _> = [(f.root, rendered)].into_iter().collect();
    let printer = AlethePrinter::new_with_overrides(&f.terms, Some(&exact));
    let inline = printer
        .format_array_row_chain(ProofId(1), &[f.packed])
        .unwrap();
    assert!(!inline.contains("(define-fun @ay_row_"));
    let hostile: HashMap<_, String> = [(f.root, "memory".into())].into_iter().collect();
    assert!(AlethePrinter::new_with_overrides(&f.terms, Some(&hostile))
        .format_array_row_chain(ProofId(1), &[f.packed])
        .is_none());
    let printer = AlethePrinter::new(&f.terms);
    printer.anchor_binder_names.borrow_mut().insert("i0".into());
    let inline = printer
        .format_array_row_chain(ProofId(1), &[f.packed])
        .unwrap();
    assert!(!inline.contains("(define-fun @ay_row_"));
}

#[test]
fn fresh_names_read_all_actual_channels_and_refuse_nonce_exhaustion() {
    let mut f = Fixture::new();
    f.terms.mk_var("@ay_row_t1.p_0_taken", Sort::Bool);
    let foreign = f.terms.mk_var("foreign", Sort::Bool);
    let overrides: HashMap<_, String> = [(foreign, "|@ay_row_t1.p_1_hidden|".into())]
        .into_iter()
        .collect();
    let printer = AlethePrinter::new_with_overrides(&f.terms, Some(&overrides));
    printer
        .skolem_overrides
        .borrow_mut()
        .insert(foreign, "|@ay_row_t1.p_2_hidden|".into());
    printer
        .let_bridge_renderings
        .borrow_mut()
        .insert(foreign, "|@ay_row_t1.p_3_hidden|".into());
    let document = printer
        .format_array_row_chain(ProofId(1), &[f.packed])
        .unwrap();
    assert!(document.contains("(define-fun @ay_row_t1.p_4_0"));
    // Every occupied candidate is a real arena spelling. No unbounded retry.
    for nonce in 2..NONCES {
        f.terms
            .mk_var(format!("@ay_row_t1.p_{nonce}_taken"), Sort::Bool);
    }
    let printer = AlethePrinter::new_with_overrides(&f.terms, Some(&overrides));
    let mut text = Text {
        printer: &printer,
        lines: Vec::new(),
        bytes: 0,
    };
    assert!(printer.row_prefix_plan("t1.p", f.root, &mut text).is_none());
}

#[test]
fn malformed_forward_and_cyclic_stores_refuse_before_rendering() {
    let array = Sort::array(Sort::bitvec(64), Sort::bitvec(8));
    for child in [TermId(0), TermId(99)] {
        let terms = TermStore::from_entries(
            vec![
                (
                    TermData::App(Symbol::named("store"), vec![child, TermId(1), TermId(2)]),
                    array.clone(),
                ),
                (TermData::Var("i".into(), 0), Sort::bitvec(64)),
                (
                    TermData::Const(Constant::BitVec {
                        value: BigInt::from(1),
                        width: 8,
                    }),
                    Sort::bitvec(8),
                ),
            ],
            None,
            None,
            1,
        );
        assert!(AlethePrinter::new(&terms)
            .row_prefix_bounds(TermId(0))
            .is_none());
    }
    let mut f = Fixture::new();
    let bad = f.terms.mk_app(
        Symbol::named("store"),
        vec![f.root, f.keys[0], f.keys[0]],
        f.terms.sort(f.root).clone(),
    );
    assert!(AlethePrinter::new(&f.terms).row_store_parts(bad).is_none());
    let outer = f.terms.mk_app(
        Symbol::named("store"),
        vec![bad, f.keys[0], f.value],
        f.terms.sort(f.root).clone(),
    );
    assert!(AlethePrinter::new(&f.terms)
        .row_prefix_bounds(outer)
        .is_none());
}

#[test]
fn resource_and_live_stop_refuse_without_installing_partial_definitions() {
    let f = Fixture::new();
    let printer = AlethePrinter::new_with_overrides_and_budget(&f.terms, None, Some(200));
    let mut text = Text {
        printer: &printer,
        lines: Vec::new(),
        bytes: 0,
    };
    assert!(printer.row_prefix_plan("t1.p", f.root, &mut text).is_none());
    assert!(printer.work_budget_exhausted());
    let polls = std::cell::Cell::new(0);
    let mut caller = || {
        polls.set(polls.get() + 1);
        polls.get() < 100
    };
    let printer = AlethePrinter::new(&f.terms).with_emission_progress(&mut caller);
    let mut text = Text {
        printer: &printer,
        lines: Vec::new(),
        bytes: 0,
    };
    assert!(printer.row_prefix_plan("t1.p", f.root, &mut text).is_none());
    assert!(printer.emission_progress.refused());
    assert_eq!(polls.get(), 100);
}

#[test]
fn incorrect_guard_or_value_cannot_reach_the_row_printer() {
    let mut f = Fixture::new();
    let mut missing = f.guards[1..].to_vec();
    missing.push(f.equality);
    assert!(AlethePrinter::new(&f.terms)
        .format_array_row_chain(ProofId(1), &missing)
        .is_none());
    let wrong = f.terms.mk_bitvec(BigInt::from(255), 8);
    let equality = f
        .terms
        .mk_app(Symbol::named("="), vec![f.read, wrong], Sort::Bool);
    let mut bad = f.guards.clone();
    bad.push(equality);
    assert!(AlethePrinter::new(&f.terms)
        .format_array_row_chain(ProofId(1), &bad)
        .is_none());
}

#[test]
fn unpacked_row_vector_and_retained_e1_prefix_preserve_original_raw_assume() {
    for (name, mut f) in [
        ("unpacked-frame-offsets", Fixture::frame_offsets()),
        ("unpacked-retained-e1-prefix", Fixture::retained_e1_prefix()),
    ] {
        let proof = f.proof_unpacked();
        crate::check_proof_strict(&proof, &f.terms)
            .expect("ordinary unpacked row validator and not_or/resolution");
        let source = crate::format_term_alethe(&f.terms, f.assumption);
        let document = crate::try_export_alethe_with_problem_scope_and_overrides(
            &proof,
            &f.terms,
            &[f.assumption],
            None,
        )
        .expect("actual production export, unchanged ordinary raw Assume");
        assert_eq!(document.matches(":rule arrays_row").count(), 79);
        assert_eq!(document.matches("(define-fun @ay_row_").count(), 80);
        assert!(document.contains(&format!("(assume t0 {source})")));
        assert!(!document.contains(":rule hole") && !document.contains(":rule trust"));
        assert!(document.len() < 16 * 1024 * 1024);
        println!("ROW_PREFIX_NATIVE_CASE name={name} problem_bytes={} proof_bytes={} whole_assume_override=false",f.original().len(),document.len());
        capture(name, &f.original(), &document);
    }
}

#[test]
fn small_whole_assume_override_stays_raw_while_prefixes_are_shared() {
    let mut f = Fixture::variables(17);
    let proof = f.proof_unpacked();
    crate::check_proof_strict(&proof, &f.terms).unwrap();
    let source = crate::format_term_alethe(&f.terms, f.assumption);
    let overrides: HashMap<_, _> = [(f.assumption, source.clone())].into_iter().collect();
    let document = crate::try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &f.terms,
        &[f.assumption],
        Some(&overrides),
    )
    .expect("small exact authored-override domain stays supported");
    assert_eq!(document.matches("(define-fun @ay_row_").count(), 17);
    assert!(document.contains(&format!("(assume t0 {source})")));
    assert!(!document.contains(":rule hole") && !document.contains(":rule trust"));
    capture(
        "seventeen-stores-whole-assume-override",
        &f.original(),
        &document,
    );
}

#[test]
fn expanded_payload_and_unrelated_inventory_are_bounded_before_copying() {
    let mut f = Fixture::new();
    let mut word = f.keys[0];
    for _ in 0..20 {
        word = f
            .terms
            .mk_app(Symbol::named("bvadd"), vec![word, word], Sort::bitvec(64));
    }
    let outer = f.terms.mk_app(
        Symbol::named("store"),
        vec![f.root, word, f.value],
        f.terms.sort(f.root).clone(),
    );
    let printer = AlethePrinter::new(&f.terms);
    assert!(printer.row_prefix_bounds(outer).is_none());
    assert!(
        printer.format_cache.borrow().is_empty(),
        "refuse expanded text before materializing it"
    );
    let foreign = f.terms.mk_var("opaque_inventory", Sort::Bool);
    let overrides: HashMap<_, String> = [(foreign, "x".repeat(MAX_NAME_BYTES + 1))]
        .into_iter()
        .collect();
    assert!(
        !AlethePrinter::new_with_overrides(&f.terms, Some(&overrides))
            .row_prefix_is_fresh("@ay_row_t1.p_0_")
    );
}

#[test]
fn binder_dependent_and_alternate_rendering_channels_do_not_define_arrays() {
    let mut f = Fixture::new();
    let condition = f
        .terms
        .mk_forall(vec![("bound".into(), Sort::Bool)], f.terms.true_term());
    let value = f
        .terms
        .mk_app(Symbol::named("opaque"), vec![condition], Sort::bitvec(8));
    let outer = f.terms.mk_app(
        Symbol::named("store"),
        vec![f.root, f.keys[0], value],
        f.terms.sort(f.root).clone(),
    );
    assert!(AlethePrinter::new(&f.terms)
        .row_prefix_bounds(outer)
        .is_none());
    let printer = AlethePrinter::new(&f.terms);
    printer
        .skolem_overrides
        .borrow_mut()
        .insert(f.root, "memory".into());
    assert!(printer.row_prefix_bounds(f.root).is_none());
    printer.skolem_overrides.borrow_mut().clear();
    printer
        .let_bridge_renderings
        .borrow_mut()
        .insert(f.root, "memory".into());
    assert!(printer.row_prefix_bounds(f.root).is_none());
}

#[test]
fn two_long_array_equality_paths_have_separate_names_and_raw_congruence() {
    let mut f = Fixture::new();
    let mut base = f.root;
    while let TermData::App(Symbol::Named(op), args) = f.terms.get(base) {
        if op != "store" {
            break;
        }
        base = args[0];
    }
    let array_sort = f.terms.sort(f.root).clone();
    let right_base = f.terms.mk_var("other_memory", array_sort.clone());
    let query = f.terms.mk_var("query", Sort::bitvec(64));
    let mut right = right_base;
    for (index, &key) in f.keys.iter().enumerate() {
        let value = f
            .terms
            .mk_bitvec(BigInt::from(if index == 0 { 8 } else { index }), 8);
        right = f.terms.mk_app(
            Symbol::named("store"),
            vec![right, key, value],
            array_sort.clone(),
        );
    }
    let array_eq = f
        .terms
        .mk_app(Symbol::named("="), vec![f.root, right], Sort::Bool);
    let premise = f.terms.mk_not_raw(array_eq);
    let left_read = f
        .terms
        .mk_app(Symbol::named("select"), vec![base, query], Sort::bitvec(8));
    let right_read = f.terms.mk_app(
        Symbol::named("select"),
        vec![right_base, query],
        Sort::bitvec(8),
    );
    let conclusion = f
        .terms
        .mk_app(Symbol::named("="), vec![left_read, right_read], Sort::Bool);
    f.guards = f
        .keys
        .iter()
        .map(|&key| {
            f.terms
                .mk_app(Symbol::named("="), vec![key, query], Sort::Bool)
        })
        .collect();
    f.declarations.push_str("\n(declare-const other_memory (Array (_ BitVec 64) (_ BitVec 8)))\n(declare-const query (_ BitVec 64))");
    let mut literals = f.guards.clone();
    literals.extend([premise, conclusion]);
    f.packed = f.terms.mk_app(Symbol::named("or"), literals, Sort::Bool);
    f.assumption = f.terms.mk_not_raw(f.packed);
    let proof = f.proof();
    crate::check_proof_strict(&proof, &f.terms).unwrap();
    let document = crate::try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &f.terms,
        &[f.assumption],
        None,
    )
    .unwrap();
    assert_eq!(document.matches("(define-fun @ay_row_").count(), 160);
    assert_eq!(document.matches(":rule arrays_row").count(), 160);
    assert!(document.contains("@ay_row_t1.l_") && document.contains("@ay_row_t1.r_"));
    assert!(!document.contains(":rule hole") && !document.contains(":rule trust"));
    capture(
        "two-eighty-store-array-equality-paths",
        &f.original(),
        &document,
    );
}
