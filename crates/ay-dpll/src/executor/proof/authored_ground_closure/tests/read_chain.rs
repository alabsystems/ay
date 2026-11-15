// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::super::facts::FactBase;
use super::*;
use crate::executor::proof::authored_ground_closure::emit::ClosureEmitter;
use crate::executor::proof::authored_ground_closure::read_chain::ReadChainState;

fn source(width: u32, stores: &[(String, u8)], key: &str, value: u8, pin: &str) -> String {
    let mut array = "a".to_string();
    for (index, value) in stores {
        array = format!("(store {array} {index} (_ bv{value} 8))");
    }
    let claim = format!("(not (= (select {array} {key}) (_ bv{value} 8)))");
    let root = if pin.is_empty() {
        claim
    } else {
        format!("(and {pin} {claim})")
    };
    format!("(set-option :produce-proofs true)\n(set-logic QF_AUFBV)\n(declare-const a (Array (_ BitVec {width}) (_ BitVec 8)))\n(declare-const x (_ BitVec {width}))\n(declare-const y (_ BitVec {width}))\n(assert {root})\n(check-sat)\n")
}

fn index(base: &str, offset: u128, width: u32) -> String {
    format!("(bvadd {base} (_ bv{offset} {width}))")
}

fn prepared(input: &str) -> (Executor, TermId) {
    let mut exec = Executor::new();
    for command in parse(input).unwrap() {
        if !matches!(command, Command::CheckSat | Command::Exit) {
            exec.execute_all(&[command]).unwrap();
        }
    }
    let surface = exec.ctx.assertions_parsed()[0].clone();
    let root = exec
        .raw_intern_shared_ground_memory_surface(&surface)
        .unwrap();
    (exec, root)
}

fn retain(name: &str, input: &str, proof: Option<&str>) {
    let dir = std::env::temp_dir().join(format!("ay-direct-read-chain-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join(format!("{name}.smt2")), input).unwrap();
    if let Some(proof) = proof {
        std::fs::write(dir.join(format!("{name}.alethe")), proof).unwrap();
    }
    println!("direct-read-chain fixture: {}", dir.join(name).display());
}

fn checked(name: &str, input: &str) -> (Executor, Proof) {
    let (mut exec, root) = prepared(input);
    let proof = exec
        .early_ground_closure_memory_candidate(root)
        .expect("direct read proof");
    assert!(proof
        .steps
        .iter()
        .all(|step| !matches!(step, ProofStep::Assume(term) if *term != root)));
    assert!(exec
        .check_proof_strict_derivation_with_datatypes(&proof)
        .unwrap()
        .is_complete());
    exec.set_alethe_dialect(ay_proof::AletheDialect::Clean);
    let overrides = exec.proof_export_term_overrides();
    let surfaces = exec.authored_export_surfaces();
    let text = exec
        .in_alethe_dialect(|| {
            ay_proof::try_export_alethe_with_authored_surfaces(
                &proof,
                &exec.ctx.terms,
                &[root],
                overrides.as_ref(),
                surfaces.channels(),
                None,
            )
        })
        .expect("complete source-scoped ROW export");
    let scope = ay_proof::ProblemScope::from_smtlib_source(input);
    ay_proof::check_alethe_document_in_dialect(&text, &scope, exec.alethe_dialect())
        .expect("the actual checker-facing document validates in its declared source scope");
    assert!(!text.contains("(declare-"));
    assert!(!text.contains(":rule hole") && !text.contains(":rule trust"));
    assert!(exec.last_proof_raw_original_assertions.is_empty());
    assert!(exec.last_proof().is_none());
    println!(
        "direct-read-chain {name}: steps={} ROW={} checked_offsets={} exported_bytes={}",
        proof.steps.len(),
        lemma_count(&proof, |kind, _| matches!(
            kind,
            TheoryLemmaKind::ArrayRowChain
        )),
        intrinsic_count(&proof, AletheRule::BvOffsetSpinesV1),
        text.len()
    );
    retain(name, input, Some(&text));
    (exec, proof)
}

fn refused(name: &str, input: &str) {
    let (mut exec, root) = prepared(input);
    assert!(exec.early_ground_closure_memory_candidate(root).is_none());
    assert!(exec.last_proof().is_none());
    assert!(exec.last_proof_raw_original_assertions.is_empty());
    retain(name, input, None);
}

#[test]
fn direct_read_chain_standalone_dump_is_not_the_checker_facing_document() {
    let input = source(
        8,
        &[(index("x", 0, 8), 7), (index("x", 1, 8), 9)],
        &index("x", 0, 8),
        7,
        "",
    );
    let (exec, proof) = checked("source-scoped-control", &input);
    let standalone = ay_proof::try_export_alethe(&proof, &exec.ctx.terms)
        .expect("standalone rendering remains a diagnostic API");
    let scope = ay_proof::ProblemScope::from_smtlib_source(&input);
    let refusal = ay_proof::check_alethe_document_in_dialect(
        &standalone,
        &scope,
        ay_proof::AletheDialect::Clean,
    )
    .expect_err("a standalone dump declares symbols and cannot be submitted as a proof");
    assert_eq!(refusal.tag(), "declaration-command");
    retain("standalone-declaration-refused", &input, Some(&standalone));
}

#[test]
fn direct_read_chain_eighty_repeated_skips_use_one_checked_row_without_suffix_reads() {
    let stores: Vec<_> = (0..80)
        .map(|n| (index("x", u128::from(n != 0), 64), (n + 1) as u8))
        .collect();
    let input = source(64, &stores, &index("x", 0, 64), 1, "");
    let (_, proof) = checked("eighty-repeated-skips", &input);
    assert_eq!(
        lemma_count(&proof, |kind, _| matches!(
            kind,
            TheoryLemmaKind::ArrayRowChain
        )),
        1
    );
    assert_eq!(intrinsic_count(&proof, AletheRule::BvOffsetSpinesV1), 1);
    let (mut exec, root) = prepared(&input);
    let mut search = GroundSearch::default();
    exec.register_ground_subterms(&mut search.closure, root)
        .unwrap();
    let nodes = search.closure.nodes().len();
    assert!(exec
        .saturate_ground_search(&mut search, &[root], &[])
        .is_some());
    assert_eq!(search.closure.nodes().len(), nodes, "no select per suffix");
    assert_eq!(search.read_chains.witnesses.len(), 1);
    assert_eq!(search.read_chains.witnesses[0].skipped.len(), 1);
}

#[test]
fn direct_read_chain_checked_skips_close_and_general_bv_representation_still_refuses() {
    let stores: Vec<_> = (0..80)
        .map(|n| (index("x", n, 64), (n + 1) as u8))
        .collect();
    let input = source(64, &stores, &index("x", 0, 64), 1, "");
    let (mut exec, root) = prepared(&input);
    let proof = exec
        .early_ground_closure_memory_candidate(root)
        .expect("a producer proposal is not authority");
    assert_eq!(
        lemma_count(&proof, |kind, _| matches!(
            kind,
            TheoryLemmaKind::ArrayRowChain
        )),
        1
    );
    assert_eq!(intrinsic_count(&proof, AletheRule::BvOffsetSpinesV1), 79);
    assert!(exec
        .check_proof_strict_derivation_with_datatypes(&proof)
        .unwrap()
        .is_complete());
    ay_proof::check_proof_strict_with_context(&proof, &exec.ctx.terms, None, None, Some(&[root]))
        .unwrap();
    let refusal = exec
        .check_proof_strict_derivation_with_datatypes(&general_bv_control(&proof))
        .expect_err("the unchanged whole-proof BV cap refuses this large candidate");
    assert!(refusal
        .to_string()
        .contains("more than 8 expensive BV steps"));
    println!("direct-read-chain eighty distinct skip refusal: {refusal}");
    assert!(exec.last_proof().is_none() && exec.last_proof_raw_original_assertions.is_empty());
    retain("eighty-distinct-skips-refused", &input, None);
}

#[test]
fn direct_read_chain_aliases_need_actual_source_equality_and_key_congruence() {
    let input = source(
        8,
        &[(index("y", 0, 8), 7), (index("x", 1, 8), 9)],
        &index("x", 0, 8),
        7,
        "(= x y)",
    );
    let (_, proof) = checked("source-alias", &input);
    assert!(intrinsic_count(&proof, AletheRule::BvOffsetSpinesV1) > 0);
    assert_eq!(
        lemma_count(&proof, |kind, clause| matches!(
            kind,
            TheoryLemmaKind::BvBitBlast
        ) && clause.len() == 2),
        0
    );
    assert!(
        lemma_count(&proof, |kind, _| matches!(
            kind,
            TheoryLemmaKind::EufCongruent
        )) > 0
    );
    refused(
        "missing-alias",
        &source(
            8,
            &[(index("y", 0, 8), 7), (index("x", 1, 8), 9)],
            &index("y", 0, 8),
            7,
            "",
        ),
    );
}

#[test]
fn direct_read_chain_latest_write_wrap_width_and_duplicate_guard_controls() {
    for width in [1, 8, 64, 128] {
        let stores = [
            (index("x", 0, width), 7),
            (index("x", 1, width), 9),
            (index("x", 1, width), 11),
        ];
        let (_, proof) = checked(
            &format!("width-{width}-duplicate"),
            &source(width, &stores, &index("x", 0, width), 7, ""),
        );
        assert_eq!(
            intrinsic_count(&proof, AletheRule::BvOffsetSpinesV1),
            1,
            "duplicate skips share a guard and unit"
        );
        let latest = [
            (index("x", 0, width), 7),
            (index("x", 1, width), 9),
            (index("x", 0, width), 11),
        ];
        checked(
            &format!("width-{width}-newest"),
            &source(width, &latest, &index("x", 0, width), 11, ""),
        );
        refused(
            &format!("width-{width}-wrong-value"),
            &source(width, &latest, &index("x", 0, width), 7, ""),
        );
        let max = u128::MAX >> (128 - width);
        let wrap = format!("(bvadd (bvadd x (_ bv{max} {width})) (_ bv1 {width}))");
        checked(
            &format!("width-{width}-wrap"),
            &source(width, &[(index("x", 0, width), 7), (wrap, 11)], "x", 11, ""),
        );
    }
}

#[test]
fn direct_read_chain_wrong_base_offset_and_unknown_latest_alias_decline() {
    let stores = [(index("x", 0, 8), 7), (index("x", 1, 8), 9)];
    refused(
        "wrong-read-base",
        &source(8, &stores, &index("y", 0, 8), 7, ""),
    );
    refused(
        "wrong-read-offset",
        &source(8, &stores, &index("x", 2, 8), 7, ""),
    );
    refused(
        "wrong-skip-offset",
        &source(
            8,
            &[(index("x", 0, 8), 7), (index("x", 0, 8), 9)],
            &index("x", 0, 8),
            7,
            "",
        ),
    );
    refused(
        "unknown-latest-alias",
        &source(
            8,
            &[(index("x", 0, 8), 7), (index("y", 1, 8), 9)],
            &index("x", 0, 8),
            7,
            "",
        ),
    );
}

#[test]
fn direct_read_chain_tail_sorts_work_and_stop_fail_closed_before_edge() {
    let input = source(
        8,
        &[(index("x", 0, 8), 7), (index("x", 1, 8), 9)],
        &index("x", 0, 8),
        7,
        "",
    );
    for stopped in [false, true] {
        let (mut exec, root) = prepared(&input);
        let mut closure = GroundClosure::default();
        exec.register_ground_subterms(&mut closure, root).unwrap();
        if stopped {
            exec.set_interrupt(std::sync::Arc::new(std::sync::atomic::AtomicBool::new(
                true,
            )));
        }
        let mut state = ReadChainState::default();
        let mut work = SharedGroundWork::new(if stopped { MAX_NODES * MAX_ROUNDS } else { 0 });
        let arena = exec.ctx.terms.len();
        assert!(exec
            .add_ground_read_chain_edges(&mut closure, &mut state, &FactBase::default(), &mut work)
            .is_none());
        assert!(closure.edges().is_empty() && state.witnesses.is_empty());
        assert_eq!(exec.ctx.terms.len(), arena);
    }
    let (mut exec, _) = prepared(&input);
    let array_sort = Sort::array(Sort::bitvec(8), Sort::bitvec(8));
    let a = exec.ctx.terms.mk_var("raw-array", array_sort.clone());
    let key = exec.ctx.terms.mk_var("raw-key", Sort::bitvec(8));
    let wrong = exec.ctx.terms.mk_bitvec(BigInt::from(1), 16);
    let value = exec.ctx.terms.mk_bitvec(BigInt::from(7), 8);
    let bad_tail =
        exec.ctx
            .terms
            .mk_app(Symbol::named("store"), [a, key, wrong], array_sort.clone());
    let outer = exec
        .ctx
        .terms
        .mk_app(Symbol::named("store"), [bad_tail, key, value], array_sort);
    let read = exec
        .ctx
        .terms
        .mk_app(Symbol::named("select"), [outer, key], Sort::bitvec(8));
    let mut closure = GroundClosure::default();
    exec.register_ground_subterms(&mut closure, read).unwrap();
    let mut state = ReadChainState::default();
    exec.add_ground_read_chain_edges(
        &mut closure,
        &mut state,
        &FactBase::default(),
        &mut SharedGroundWork::new(MAX_NODES * MAX_ROUNDS),
    )
    .unwrap();
    assert!(
        closure.edges().is_empty() && state.witnesses.is_empty(),
        "the overwritten malformed suffix is still rejected"
    );
}

#[test]
fn direct_read_chain_scope_stamp_and_emission_step_limit_are_enforced() {
    let input = source(
        8,
        &[(index("x", 0, 8), 7), (index("x", 1, 8), 9)],
        &index("x", 0, 8),
        7,
        "",
    );
    let (mut exec, root) = prepared(&input);
    let mut search = GroundSearch::default();
    exec.register_ground_subterms(&mut search.closure, root)
        .unwrap();
    exec.add_ground_read_chain_edges(
        &mut search.closure,
        &mut search.read_chains,
        &search.facts,
        &mut SharedGroundWork::new(MAX_NODES * MAX_ROUNDS),
    )
    .unwrap();
    let edge = *search.closure.edges().last().unwrap();
    let EdgeReason::ReadChain(witness) = edge.reason else {
        panic!("direct edge")
    };
    let literal = exec
        .ctx
        .terms
        .mk_app(Symbol::named("="), [edge.a, edge.b], Sort::Bool);
    assert!(
        search.read_chains.current(&exec.ctx),
        "append-only constructors are allowed"
    );
    let arena = exec.ctx.terms.len();
    let mut emitter = ClosureEmitter::new(&search);
    for _ in 0..16_384 {
        emitter.proof.add_assume(root, None);
    }
    assert!(exec
        .emit_ground_read_chain(&mut emitter, edge, literal, 0, witness)
        .is_none());
    assert_eq!(emitter.proof.steps.len(), 16_384);
    assert_eq!(
        exec.ctx.terms.len(),
        arena,
        "refusal precedes proof-only read allocation"
    );
    exec.execute_all(&parse("(push 1)").unwrap()).unwrap();
    assert!(!search.read_chains.current(&exec.ctx));
    let mut emitter = ClosureEmitter::new(&search);
    assert!(exec
        .emit_ground_read_chain(&mut emitter, edge, literal, 0, witness)
        .is_none());
    assert!(emitter.proof.steps.is_empty());
    exec.execute_all(&parse("(pop 1)").unwrap()).unwrap();
    assert!(
        !search.read_chains.current(&exec.ctx),
        "rollback never revives a session cache"
    );
}

#[test]
fn direct_read_chain_popped_source_alias_cannot_be_reused() {
    let input = source(
        8,
        &[(index("y", 0, 8), 7), (index("x", 1, 8), 9)],
        &index("y", 0, 8),
        7,
        "",
    );
    let input = input.replace("(check-sat)", "(push 1)\n(assert (= x y))\n(check-sat)");
    let mut exec = solved(&input, "unsat");
    exec.check_proof_strict_with_datatypes(exec.last_proof().unwrap())
        .unwrap();
    assert_eq!(
        exec.execute_all(&parse("(pop 1)(check-sat)").unwrap())
            .unwrap(),
        ["sat"]
    );
    assert!(exec.last_proof().is_none());
}

#[test]
fn direct_read_chain_missing_guard_and_forged_value_are_strictly_rejected() {
    let input = source(
        8,
        &[(index("x", 0, 8), 7), (index("x", 1, 8), 9)],
        &index("x", 0, 8),
        7,
        "",
    );
    let (mut exec, proof) = checked("forgery-control", &input);
    for missing_guard in [true, false] {
        let mut forged = proof.clone();
        let row = forged
            .steps
            .iter_mut()
            .find_map(|step| match step {
                ProofStep::TheoryLemma {
                    clause,
                    kind: TheoryLemmaKind::ArrayRowChain,
                    ..
                } => Some(clause),
                _ => None,
            })
            .unwrap();
        if missing_guard {
            row.remove(0);
        } else {
            let conclusion = *row.last().unwrap();
            let (read, _) = decode_eq_local(&exec.ctx.terms, conclusion).unwrap();
            let wrong = exec.ctx.terms.mk_bitvec(BigInt::from(8), 8);
            *row.last_mut().unwrap() =
                exec.ctx
                    .terms
                    .mk_app(Symbol::named("="), [read, wrong], Sort::Bool);
        }
        assert!(exec
            .check_proof_strict_derivation_with_datatypes(&forged)
            .is_err());
    }
}

#[test]
fn direct_read_chain_cached_alias_guard_needs_earlier_edges_in_each_explanation() {
    let input = source(
        8,
        &[(index("y", 0, 8), 7), (index("x", 1, 8), 9)],
        &index("y", 0, 8),
        7,
        "(= x y)",
    );
    let (mut exec, root) = prepared(&input);
    let mut search = GroundSearch::default();
    exec.register_ground_subterms(&mut search.closure, root)
        .unwrap();
    let _ = exec.saturate_ground_search(&mut search, &[root], &[]);
    let (limit, edge, witness) = search
        .closure
        .edges()
        .iter()
        .enumerate()
        .find_map(|(i, edge)| match edge.reason {
            EdgeReason::ReadChain(witness) => Some((i, *edge, witness)),
            _ => None,
        })
        .unwrap();
    assert!(limit > 0);
    let literal = exec
        .ctx
        .terms
        .mk_app(Symbol::named("="), [edge.a, edge.b], Sort::Bool);
    let mut emitter = ClosureEmitter::new(&search);
    assert!(exec
        .emit_ground_read_chain(&mut emitter, edge, literal, limit, witness)
        .is_some());
    assert!(!emitter.read_index_units.is_empty());
    let before = emitter.proof.steps.len();
    assert!(exec
        .emit_ground_read_chain(&mut emitter, edge, literal, 0, witness)
        .is_none());
    assert_eq!(
        emitter.proof.steps.len(),
        before,
        "the cache cannot hide a missing source-alias explanation"
    );
    assert!(
        !search.read_chains.current(&exec.ctx.clone()),
        "a copied source context is foreign"
    );
    let terms = exec.ctx.terms.clone();
    exec.ctx.terms = terms;
    assert!(
        !search.read_chains.current(&exec.ctx),
        "a copied term universe is foreign"
    );
}

fn alias_chain_source(width: u32, relation: &str, claimed: u8) -> String {
    format!(
        "(set-option :produce-proofs true)(set-logic QF_ABV)
         (declare-fun a () (Array (_ BitVec {width}) (_ BitVec 8)))
         (declare-fun b () (Array (_ BitVec {width}) (_ BitVec 8)))
         (declare-fun c () (Array (_ BitVec {width}) (_ BitVec 8)))
         (declare-fun x () (_ BitVec {width}))
         (declare-fun y () (_ BitVec {width}))
         (assert (and (= b (store a x (_ bv7 8)))
           (= c (store b y (_ bv9 8))) {relation}
           (not (= (select c x) (_ bv{claimed} 8))))) (check-sat)"
    )
}

#[test]
fn direct_read_chain_all_miss_reaches_the_exact_base_read() {
    for width in [1, 8, 64, 128] {
        let input = format!(
            "(set-option :produce-proofs true)(set-logic QF_ABV)
             (declare-const a (Array (_ BitVec {width}) (_ BitVec 8)))
             (declare-const x (_ BitVec {width}))
             (assert (not (= (select (store a (bvadd x (_ bv1 {width})) (_ bv9 8)) x)
                            (select a x)))) (check-sat)"
        );
        let (_, proof) = checked(&format!("all-miss-width-{width}-unsat"), &input);
        assert_eq!(intrinsic_count(&proof, AletheRule::BvOffsetSpinesV1), 1);
        assert_eq!(
            lemma_count(&proof, |kind, _| matches!(
                kind,
                TheoryLemmaKind::ArrayRowChain
            )),
            1
        );
    }
}

#[test]
fn direct_read_chain_all_miss_crosses_authored_array_and_offset_aliases() {
    for width in [1, 8, 64, 128] {
        let relation = format!("(= y (bvadd x (_ bv1 {width})))");
        let input = alias_chain_source(width, &relation, 7);
        let (_, proof) = checked(&format!("all-miss-alias-width-{width}-unsat"), &input);
        assert!(intrinsic_count(&proof, AletheRule::BvOffsetSpinesV1) > 0);
        assert!(intrinsic_count(&proof, AletheRule::Cong) > 0);
        assert_eq!(
            lemma_count(&proof, |kind, _| matches!(
                kind,
                TheoryLemmaKind::BvBitBlast
            )),
            0,
            "source aliases are transported to the checked scalar identity"
        );
    }
    for (name, relation, value) in [
        ("all-miss-missing-alias-sat", "", 7),
        ("all-miss-overlap-sat", "(= y (bvadd x (_ bv0 8)))", 7),
        ("all-miss-wrong-value-sat", "(= y (bvadd x (_ bv1 8)))", 9),
    ] {
        let input = alias_chain_source(8, relation, value);
        refused(name, &input);
        let (mut exec, _) = prepared(&input);
        assert_eq!(
            exec.execute_all(&parse("(check-sat)").unwrap()).unwrap(),
            ["sat"],
            "a missing or overlapping source relation cannot become a skip"
        );
    }
}

#[test]
fn direct_read_chain_all_miss_adds_one_base_read_and_shares_repeated_guards() {
    let mut array = "a".to_string();
    for value in 0..80 {
        array = format!("(store {array} (bvadd x (_ bv1 64)) (_ bv{value} 8))");
    }
    let input = format!(
        "(set-option :produce-proofs true)(set-logic QF_ABV)
         (declare-const a (Array (_ BitVec 64) (_ BitVec 8)))
         (declare-const x (_ BitVec 64))
         (assert (not (= (select {array} x) (select a x)))) (check-sat)"
    );
    let (mut exec, root) = prepared(&input);
    let mut search = GroundSearch::default();
    exec.register_ground_subterms(&mut search.closure, root)
        .unwrap();
    let nodes = search.closure.nodes().len();
    assert!(exec
        .saturate_ground_search(&mut search, &[root], &[])
        .is_some());
    assert_eq!(
        search.closure.nodes().len(),
        nodes,
        "the base read is authored already"
    );
    assert_eq!(search.read_chains.witnesses.len(), 1);
    assert_eq!(search.read_chains.witnesses[0].skipped.len(), 1);
    let (_, proof) = checked("all-miss-eighty-repeated-unsat", &input);
    assert_eq!(intrinsic_count(&proof, AletheRule::BvOffsetSpinesV1), 1);
}

#[test]
fn direct_read_chain_image_guard_cache_cannot_hide_a_future_source_edge() {
    let input = alias_chain_source(8, "(= y (bvadd x (_ bv1 8)))", 7);
    let (mut exec, root) = prepared(&input);
    let mut search = GroundSearch::default();
    exec.register_ground_subterms(&mut search.closure, root)
        .unwrap();
    assert!(exec
        .saturate_ground_search(&mut search, &[root], &[])
        .is_some());
    let (limit, edge, witness) = search
        .closure
        .edges()
        .iter()
        .enumerate()
        .find_map(|(i, e)| {
            let EdgeReason::ReadChain(w) = e.reason else {
                return None;
            };
            matches!(
                search.read_chains.witnesses[w].end,
                super::super::read_chain::ReadChainEnd::Base(_)
            )
            .then_some((i, *e, w))
        })
        .unwrap();
    let literal = exec
        .ctx
        .terms
        .mk_app(Symbol::named("="), [edge.a, edge.b], Sort::Bool);
    let mut emitter = ClosureEmitter::new(&search);
    assert!(exec
        .emit_ground_read_chain(&mut emitter, edge, literal, limit, witness)
        .is_some());
    let steps = emitter.proof.steps.len();
    assert!(exec
        .emit_ground_read_chain(&mut emitter, edge, literal, 0, witness)
        .is_none());
    assert_eq!(
        emitter.proof.steps.len(),
        steps,
        "no cached source-image authority"
    );
}

#[test]
fn direct_read_chain_all_miss_forged_guard_or_base_is_rejected() {
    let input = alias_chain_source(8, "(= y (bvadd x (_ bv1 8)))", 7);
    let (mut exec, proof) = checked("all-miss-forgery-unsat", &input);
    for remove_guard in [true, false] {
        let mut forged = proof.clone();
        let row = forged
            .steps
            .iter_mut()
            .find_map(|step| match step {
                ProofStep::TheoryLemma {
                    kind: TheoryLemmaKind::ArrayRowChain,
                    clause,
                    ..
                } => Some(clause),
                _ => None,
            })
            .unwrap();
        if remove_guard {
            let _ = row.remove(0);
        } else {
            let conclusion = *row.last().unwrap();
            let (left, _) = decode_eq_local(&exec.ctx.terms, conclusion).unwrap();
            let wrong = exec.ctx.terms.mk_bitvec(0.into(), 8);
            *row.last_mut().unwrap() =
                exec.ctx
                    .terms
                    .mk_app(Symbol::named("="), [left, wrong], Sort::Bool);
        }
        assert!(exec
            .check_proof_strict_derivation_with_datatypes(&forged)
            .is_err());
    }
}

#[test]
fn direct_read_chain_all_miss_normalizes_the_source_alias_inside_each_store_key() {
    let mut first = "a".to_string();
    let mut second = "b".to_string();
    for offset in 0..8 {
        first = format!("(store {first} (bvadd x (_ bv{offset} 64)) (_ bv{offset} 8))");
        second = format!(
            "(store {second} (bvadd y (_ bv{offset} 64)) (_ bv{} 8))",
            offset + 16
        );
    }
    let input = format!(
        "(set-option :produce-proofs true)(set-logic QF_ABV)
         (declare-const a (Array (_ BitVec 64) (_ BitVec 8)))
         (declare-const b (Array (_ BitVec 64) (_ BitVec 8)))
         (declare-const c (Array (_ BitVec 64) (_ BitVec 8)))
         (declare-const x (_ BitVec 64))(declare-const y (_ BitVec 64))
         (assert (and (= b {first}) (= c {second}) (= y (bvadd x (_ bv8 64)))
           (not (= (select c (bvadd x (_ bv3 64))) (_ bv3 8))))) (check-sat)"
    );
    let (_, proof) = checked("all-miss-two-word-spines-unsat", &input);
    assert!(intrinsic_count(&proof, AletheRule::BvOffsetSpinesV1) >= 8);
    assert_eq!(
        lemma_count(&proof, |kind, _| matches!(
            kind,
            TheoryLemmaKind::BvBitBlast
        )),
        0
    );
}

#[test]
fn direct_read_chain_all_miss_keeps_an_opaque_array_ite_base_intact() {
    let prefix = "(set-option :produce-proofs true)(set-logic QF_ABV)
        (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const b (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const g Bool)(declare-const x (_ BitVec 8))";
    let input = format!(
        "{prefix}
        (assert (not (= (select (store (ite g a b) (bvadd x (_ bv1 8)) (_ bv9 8)) x)
                       (select (ite g a b) x)))) (check-sat)"
    );
    checked("all-miss-opaque-ite-base-unsat", &input);
    let wrong = format!(
        "{prefix}
        (assert (not (= (select (store (ite g a b) (bvadd x (_ bv1 8)) (_ bv9 8)) x)
                       (select a x)))) (check-sat)"
    );
    refused("all-miss-opaque-ite-wrong-world-sat", &wrong);
}

#[test]
fn direct_read_chain_existing_direct_offsets_precede_optional_literal_images() {
    let stores: Vec<_> = (0..12)
        .map(|offset| (index("x", offset, 8), (offset + 1) as u8))
        .collect();
    let facts: Vec<_> = (0..12)
        .map(|offset| format!("(= {} (_ bv{offset} 8))", index("x", offset, 8)))
        .collect();
    let input = source(
        8,
        &stores,
        &index("x", 0, 8),
        1,
        &format!("(and {})", facts.join(" ")),
    );
    let (_, proof) = checked("direct-image-priority-unsat", &input);
    assert_eq!(intrinsic_count(&proof, AletheRule::BvOffsetSpinesV1), 11);
    assert_eq!(
        lemma_count(&proof, |kind, _| matches!(
            kind,
            TheoryLemmaKind::BvBitBlast
        )),
        0,
        "optional class images do not replace supported offsets with expensive closed BV steps"
    );
}
fn aliased_fallthrough(pin: &str) -> String {
    format!(
        "(set-option :produce-proofs true)(set-logic QF_ABV)
    (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
    (declare-const middle (Array (_ BitVec 8) (_ BitVec 8)))
    (declare-const final (Array (_ BitVec 8) (_ BitVec 8)))
    (declare-const x (_ BitVec 8))(declare-const y (_ BitVec 8))
    (assert (and (= middle (store a x #x11)) (= final (store middle y #x22))
        {pin} (not (= (select final x) #x11))))(check-sat)"
    )
}

#[test]
fn all_skipped_chain_reaches_an_older_aliased_store_with_checked_index_transport() {
    for (name, pin) in [
        ("fallthrough-forward", "(= y (bvadd x #x01))"),
        ("fallthrough-reversed", "(= (bvadd x #x01) y)"),
        ("fallthrough-wrap", "(= y (bvadd x #xff))"),
    ] {
        let input = aliased_fallthrough(pin);
        let (exec, proof) = checked(name, &input);
        assert!(
            lemma_count(&proof, |kind, _| matches!(
                kind,
                TheoryLemmaKind::ArrayRowChain
            )) >= 1
        );
        assert!(intrinsic_count(&proof, AletheRule::BvOffsetSpinesV1) >= 1);
        assert!(exec.last_proof_raw_original_assertions.is_empty());
    }
}

#[test]
fn all_skipped_chain_requires_disjointness_and_the_actual_source_alias() {
    for (name, pin) in [
        ("fallthrough-unpinned", "true"),
        ("fallthrough-overlap", "(= y (bvadd x #x00))"),
    ] {
        let input = aliased_fallthrough(pin);
        refused(name, &input);
        let mut executor = Executor::new();
        let outputs = executor.execute_all(&parse(&input).unwrap()).unwrap();
        assert_eq!(outputs, ["sat"], "{name}: {:?}", executor.unknown_reason());
    }
}

#[test]
fn unproved_fallthrough_and_retired_work_add_no_read_or_authority() {
    let input = source(8, &[("y".into(), 9)], "x", 7, "");
    let (mut exec, root) = prepared(&input);
    let mut closure = GroundClosure::default();
    exec.register_ground_subterms(&mut closure, root).unwrap();
    let mut state = ReadChainState::default();
    let before = exec.ctx.terms.len();
    let mut work = SharedGroundWork::new(work::MAX_SHARED_WORK);
    exec.add_ground_read_chain_edges(&mut closure, &mut state, &FactBase::default(), &mut work)
        .unwrap();
    assert_eq!(exec.ctx.terms.len(), before);
    assert!(state.witnesses.is_empty());
    let mut work = SharedGroundWork::new(0);
    assert!(exec
        .add_ground_read_chain_edges(&mut closure, &mut state, &FactBase::default(), &mut work)
        .is_none());
    assert_eq!(exec.ctx.terms.len(), before);
    assert!(exec.last_proof().is_none() && exec.last_proof_raw_original_assertions.is_empty());
}

#[test]
fn unknown_fallthrough_charges_only_the_examined_guard_prefix() {
    let stores: Vec<_> = (0..80).map(|value| ("y".into(), value)).collect();
    let input = source(8, &stores, "x", 7, "");
    let (mut exec, root) = prepared(&input);
    let mut closure = GroundClosure::default();
    exec.register_ground_subterms(&mut closure, root).unwrap();
    let mut state = ReadChainState::default();
    // The initial read scan, complete typed chain and hit map are still paid.
    // Only one actual guard is inspected before its unknown relation declines.
    let mut work = SharedGroundWork::new(closure.nodes().len() + 2 * stores.len() + 16);
    let before = exec.ctx.terms.len();
    exec.add_ground_read_chain_edges(&mut closure, &mut state, &FactBase::default(), &mut work)
        .unwrap();
    assert!(!work.refused());
    assert!(state.witnesses.is_empty());
    assert_eq!(exec.ctx.terms.len(), before);
}

// Original ordinary ExternalCodegen source/caller proof part, byte-for-byte SHA256
// 078b6c0299fd3f6b67e2b021ea4368f33e965a9d6fa186c1643bc656ab7cc27e.
// The protected e7d6 SDK computed UNSAT but mandatory strict certification
// refused hole t1. No assertion/result/array memory is substituted here.
const ORIGINAL_CG_PROLOGUE_BYTE: &str = include_str!("readonly-cg-prologue-byte.smt2");

fn opaque_guarded_fallthrough(omit: Option<usize>, wrong: Option<usize>) -> String {
    let mut text = String::from(
        "(set-option :produce-proofs true)\n(set-logic QF_ABV)\n(declare-const a (Array (_ BitVec 64) (_ BitVec 8)))\n(declare-const p (_ BitVec 64))\n(declare-const other (_ BitVec 64))\n",
    );
    let mut array = "a".to_string();
    let mut guards = Vec::new();
    for index in 0..80 {
        text.push_str(&format!("(declare-const key{index} (_ BitVec 64))\n"));
        array = format!("(store {array} key{index} (_ bv{} 8))", index + 1);
        if omit != Some(index) {
            let key = if wrong == Some(index) {
                "other".to_string()
            } else {
                format!("key{index}")
            };
            guards.push(format!("(not (= p {key}))"));
        }
    }
    guards.push(format!("(not (= (select {array} p) (select a p)))"));
    while guards.len() > 1 {
        let mut next = Vec::new();
        let mut terms = guards.into_iter();
        while let Some(left) = terms.next() {
            next.push(match terms.next() {
                Some(right) => format!("(and {left} {right})"),
                None => left,
            });
        }
        guards = next;
    }
    text.push_str(&format!("(assert {})\n(check-sat)\n", guards[0]));
    text.replace(
        "\n", "
",
    )
}

#[test]
fn direct_read_chain_uses_owned_opaque_disequalities_for_all_eighty_stores() {
    let input = opaque_guarded_fallthrough(None, None);
    let (_, proof) = checked("opaque-authored-guards-eighty", &input);
    assert!(proof.steps.iter().any(|step| matches!(
        step,
        ProofStep::Step {
            rule: AletheRule::AndPos(_),
            ..
        }
    )));
}

#[test]
fn direct_read_chain_missing_or_foreign_guard_cannot_authorize_fallthrough() {
    for (name, input) in [
        (
            "missing-authored-guard",
            opaque_guarded_fallthrough(Some(37), None),
        ),
        (
            "foreign-authored-guard",
            opaque_guarded_fallthrough(None, Some(37)),
        ),
    ] {
        refused(name, &input);
    }
}

#[test]
fn direct_read_chain_replays_exact_original_cg_prologue_byte() {
    let _ = checked("original-cg-prologue-byte", ORIGINAL_CG_PROLOGUE_BYTE);
}

#[test]
fn public_strict_original_cg_prologue_byte_exports_no_holes() {
    let input = format!(
        "(set-option :produce-proofs true)
(set-option :check-proofs-strict true)
{ORIGINAL_CG_PROLOGUE_BYTE}"
    );
    let mut executor = Executor::new();
    let mut outputs = Vec::new();
    for command in parse(&input).unwrap() {
        if matches!(command, Command::Exit) {
            continue;
        }
        if let Some(output) = executor.execute_authored(&command).unwrap() {
            outputs.push(output);
        }
    }
    assert!(
        outputs.iter().any(|output| output == "unsat"),
        "{outputs:?}"
    );
    assert!(
        !outputs.iter().any(|output| output == "unknown"),
        "{outputs:?}"
    );
    let proof = executor
        .last_proof()
        .expect("actual strict original-input proof");
    assert!(Executor::proof_derives_empty_clause(proof));
    assert!(executor
        .check_proof_strict_with_datatypes(proof)
        .unwrap()
        .is_complete());
    let mut bytes = Vec::new();
    executor
        .try_export_last_proof_alethe_for_problem_scope_to(&mut bytes)
        .unwrap()
        .expect("strict source-scoped export");
    let text = String::from_utf8(bytes).unwrap();
    assert!(!text.contains(":rule hole") && !text.contains(":rule trust"));
}

#[test]
fn direct_read_chain_authored_disequality_orientation_is_not_authority() {
    let input =
        opaque_guarded_fallthrough(None, None).replacen("(not (= p key0))", "(not (= key0 p))", 1);
    let _ = checked("reversed-authored-guard", &input);
}
