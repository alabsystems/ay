// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::executor::proof::authored_ground_closure::emit::ClosureEmitter;
use crate::executor::proof::authored_ground_closure::packing::PackingState;

fn memory_fixture() -> String {
    let mut array = "memory".to_string();
    for byte in 0..8 {
        array = format!(
            "(store {array} (_ bv{byte} 64) ((_ extract {} {}) w0))",
            8 * byte + 7,
            8 * byte
        );
    }
    let mut parts = Vec::new();
    for byte in 0..8 {
        let value = format!("((_ zero_extend 56) (select {array} (_ bv{byte} 64)))");
        parts.push(if byte == 0 {
            value
        } else {
            format!("(bvshl {value} (_ bv{} 64))", 8 * byte)
        });
    }
    let mut packed = parts.remove(0);
    for value in parts {
        packed = format!("(bvor {packed} {value})");
    }
    format!("(set-option :produce-proofs true)\n(set-logic QF_AUFBV)\n(declare-const w0 (_ BitVec 64))\n(declare-const memory (Array (_ BitVec 64) (_ BitVec 8)))\n(assert (not (= true (= {packed} w0))))\n(check-sat)\n")
}

fn fixture(width: u32, chunk: u32, words: usize, aliases: bool, defect: &str) -> String {
    let mut declarations = String::new();
    let mut pins = Vec::new();
    let mut goals = Vec::new();
    for word in 0..words {
        declarations.push_str(&format!("(declare-const w{word} (_ BitVec {width}))\n(declare-const other{word} (_ BitVec {width}))\n"));
        if defect == "word-alias" {
            pins.push(format!("(= other{word} w{word})"));
        }
        let count = width / chunk;
        let mut parts = Vec::new();
        for part in 0..count {
            let actual_chunk = if defect == "width" { chunk / 2 } else { chunk };
            let low = if defect == "slice" && part == 0 {
                chunk
            } else {
                part * chunk
            };
            let base = if matches!(defect, "base" | "word-alias") && part % 2 == 1 {
                format!("other{word}")
            } else {
                format!("w{word}")
            };
            let extraction = format!("((_ extract {} {low}) {base})", low + actual_chunk - 1);
            let value = if aliases {
                declarations.push_str(&format!(
                    "(declare-const b{word}_{part} (_ BitVec {actual_chunk}))\n"
                ));
                pins.push(format!("(= b{word}_{part} {extraction})"));
                format!("b{word}_{part}")
            } else {
                extraction
            };
            let value = format!("((_ zero_extend {}) {value})", width - actual_chunk);
            let shift = if defect == "shift" && part == 1 {
                width
            } else if defect == "overlap" && part == 1 {
                chunk / 2
            } else {
                part * chunk
            };
            let value = if shift == 0 {
                value
            } else {
                format!("(bvshl {value} (_ bv{shift} {width}))")
            };
            parts.push(value);
        }
        // Move values across field positions while retaining the original
        // shifts, so an order mutation is a real counterexample.
        if defect == "order" {
            parts[0] = format!(
                "((_ zero_extend {}) ((_ extract {} {chunk}) w{word}))",
                width - chunk,
                2 * chunk - 1
            );
            parts[1] = format!(
                "(bvshl ((_ zero_extend {}) ((_ extract {} 0) w{word})) (_ bv{chunk} {width}))",
                width - chunk,
                chunk - 1
            );
        }
        if defect == "gap" {
            let _ = parts.pop();
        }
        let op = if defect == "operator" {
            "bvand"
        } else {
            "bvor"
        };
        let mut packed = parts.remove(0);
        for part in parts {
            packed = format!("({op} {packed} {part})");
        }
        if count == 1 {
            packed = format!("({op} {packed} (_ bv0 {width}))");
        }
        goals.push(format!("(= {packed} w{word})"));
    }
    let goal = if goals.len() == 1 {
        goals.remove(0)
    } else {
        format!("(and {})", goals.join(" "))
    };
    pins.push(format!("(not (= true {goal}))"));
    let root = if pins.len() == 1 {
        pins.remove(0)
    } else {
        format!("(and {})", pins.join(" "))
    };
    format!("(set-option :produce-proofs true)\n(set-logic QF_AUFBV)\n{declarations}(assert {root})\n(check-sat)\n")
}

pub(super) fn prepared(input: &str) -> (Executor, TermId) {
    let mut exec = Executor::new();
    for command in parse(input).unwrap() {
        if !matches!(command, Command::CheckSat | Command::Exit) {
            exec.execute_all(&[command]).unwrap();
        }
    }
    let source = exec.ctx.assertions_parsed()[0].clone();
    let root = exec
        .raw_intern_ground_bv_surface(&source)
        .or_else(|| exec.raw_intern_shared_ground_memory_surface(&source))
        .expect("the existing pure-BV or memory source contract applies");
    (exec, root)
}

pub(super) fn retain(name: &str, input: &str, proof: Option<&str>) {
    let dir = std::env::var_os("AY_CHECKED_GROUND_EMIT_ARTIFACT_DIR")
        .map(std::path::PathBuf::from)
        .unwrap_or_else(|| {
            std::env::temp_dir().join(format!("ay-packed-word-producer-{}", std::process::id()))
        });
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join(format!("{name}.smt2")), input).unwrap();
    if let Some(proof) = proof {
        std::fs::write(dir.join(format!("{name}.alethe")), proof).unwrap();
    }
    println!("packed-word fixture: {}", dir.join(name).display());
}

fn checked(name: &str, input: &str) -> (Executor, Proof) {
    let (mut exec, root) = prepared(input);
    retain(name, input, None);
    let proof = exec
        .early_ground_closure_memory_candidate(root)
        .expect("packing candidate");
    assert!(proof
        .steps
        .iter()
        .all(|s| !matches!(s,ProofStep::Assume(t) if *t!=root)));
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
        .unwrap();
    ay_proof::check_alethe_document_in_dialect(
        &text,
        &ay_proof::ProblemScope::from_smtlib_source(input),
        exec.alethe_dialect(),
    )
    .unwrap();
    assert!(
        !text.contains(":rule hole")
            && !text.contains(":rule trust")
            && !text.contains("(declare-")
    );
    assert!(exec.last_proof_raw_original_assertions.is_empty() && exec.last_proof().is_none());
    retain(name, input, Some(&text));
    println!(
        "packed-word {name}: steps={} BV={} Cong={} Trans={} bytes={}",
        proof.steps.len(),
        lemma_count(&proof, |kind, _| matches!(
            kind,
            TheoryLemmaKind::BvBitBlast
        )),
        proof
            .steps
            .iter()
            .filter(|s| matches!(
                s,
                ProofStep::Step {
                    rule: AletheRule::Cong,
                    ..
                }
            ))
            .count(),
        proof
            .steps
            .iter()
            .filter(|s| matches!(
                s,
                ProofStep::Step {
                    rule: AletheRule::Trans,
                    ..
                }
            ))
            .count(),
        text.len()
    );
    (exec, proof)
}

#[test]
fn packing_uses_earlier_byte_equalities_and_proof_only_contexts() {
    let input = fixture(64, 8, 1, true, "");
    let (_, proof) = checked("byte-alias-composed-positive", &input);
    assert!(proof.steps.iter().any(|s| matches!(
        s,
        ProofStep::Step {
            rule: AletheRule::Cong,
            ..
        }
    )));
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
        "pure contexts are not registered"
    );
    assert_eq!(search.packings.witnesses.len(), 1);
}

#[test]
fn packing_composes_with_checked_store_reads_on_arbitrary_entry_memory() {
    checked("memory-composed-positive", &memory_fixture());
}

#[test]
fn packing_pure_words_cover_existing_width_boundaries() {
    for (width, chunk) in [(1, 1), (8, 4), (64, 8), (128, 16)] {
        checked(
            &format!("pure-{width}"),
            &fixture(width, chunk, 1, false, ""),
        );
    }
}

#[test]
fn packing_word_aliases_have_real_source_explanations() {
    checked(
        "word-alias-composed-positive",
        &fixture(64, 8, 1, true, "word-alias"),
    );
    let input = fixture(64, 8, 1, true, "base");
    let (mut exec, root) = prepared(&input);
    assert!(exec.early_ground_closure_memory_candidate(root).is_none());
    retain("missing-word-alias-sat", &input, None);
}

#[test]
fn packing_source_alias_does_not_survive_pop() {
    let input = fixture(8, 4, 1, true, "base").replace(
        "(check-sat)",
        "(push 1)\n(assert (= other0 w0))\n(check-sat)",
    );
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
fn packing_wrong_slice_order_shift_overlap_gap_base_width_operator_decline() {
    for defect in [
        "slice", "order", "shift", "overlap", "gap", "base", "width", "operator",
    ] {
        let input = fixture(64, 8, 1, false, defect);
        let (mut exec, root) = prepared(&input);
        assert!(
            exec.early_ground_closure_memory_candidate(root).is_none(),
            "{defect}"
        );
        assert!(exec.last_proof().is_none() && exec.last_proof_raw_original_assertions.is_empty());
        retain(&format!("wrong-{defect}-sat"), &input, None);
    }
}

#[test]
fn packing_checked_intrinsics_and_shared_general_wiring_close_the_packet() {
    for words in [2, 9] {
        let input = fixture(64, 8, words, false, "");
        let (mut exec, root) = prepared(&input);
        let candidate = exec
            .early_ground_closure_memory_candidate(root)
            .expect("proposals are not authority");
        assert_eq!(
            intrinsic_count(&candidate, AletheRule::BvReconstructV1),
            words
        );
        assert!(exec
            .check_proof_strict_derivation_with_datatypes(&candidate)
            .unwrap()
            .is_complete());
        ay_proof::check_proof_strict_with_context(
            &candidate,
            &exec.ctx.terms,
            None,
            None,
            Some(&[root]),
        )
        .unwrap();
        let general = general_bv_control(&candidate);
        // Incoming shared wiring also closes the exact Boolean-wrapped
        // legacy representation. Keep its earlier refusal in the receipt;
        // require complete replay and actual source authority for both routes.
        assert!(exec
            .check_proof_strict_derivation_with_datatypes(&general)
            .unwrap()
            .is_complete());
        ay_proof::check_proof_strict_with_context(
            &general,
            &exec.ctx.terms,
            None,
            None,
            Some(&[root]),
        )
        .unwrap();
        assert!(exec.last_proof().is_none() && exec.last_proof_raw_original_assertions.is_empty());
        retain(
            &format!("{words}-identities-default-wiring-unsat"),
            &input,
            None,
        );
    }
}

#[test]
fn packing_precharges_source_work_and_shares_proposal_admission() {
    let input = fixture(64, 8, 1, false, "");
    for stopped in [false, true] {
        let (mut exec, root) = prepared(&input);
        let mut closure = GroundClosure::default();
        exec.register_ground_subterms(&mut closure, root).unwrap();
        let arena = exec.ctx.terms.len();
        if stopped {
            exec.set_interrupt(std::sync::Arc::new(std::sync::atomic::AtomicBool::new(
                true,
            )));
        }
        let mut state = PackingState::default();
        let mut work = SharedGroundWork::new(if stopped { MAX_NODES * MAX_ROUNDS } else { 0 });
        let mut proposals = 512;
        assert!(exec
            .add_ground_packing_edges(&mut closure, &mut state, &mut proposals, &mut work)
            .is_none());
        assert!(closure.edges().is_empty() && state.witnesses.is_empty());
        assert_eq!(exec.ctx.terms.len(), arena);
    }
    let (mut exec, root) = prepared(&input);
    let mut closure = GroundClosure::default();
    exec.register_ground_subterms(&mut closure, root).unwrap();
    let mut state = PackingState::default();
    let mut work = SharedGroundWork::new(MAX_NODES * MAX_ROUNDS);
    exec.add_ground_packing_edges(&mut closure, &mut state, &mut 0, &mut work)
        .unwrap();
    assert_eq!(work.remaining(), MAX_NODES * MAX_ROUNDS);
    assert!(state.witnesses.is_empty());
    let mut proposals = 1;
    exec.add_ground_packing_edges(&mut closure, &mut state, &mut proposals, &mut work)
        .unwrap();
    assert_eq!(proposals, 0);
    assert_eq!(state.witnesses.len(), 1);
}

#[test]
fn packing_stale_forged_future_and_step_exhausted_witnesses_fail_closed() {
    let input = fixture(64, 8, 1, true, "");
    let (mut exec, root) = prepared(&input);
    let mut search = GroundSearch::default();
    exec.register_ground_subterms(&mut search.closure, root)
        .unwrap();
    let _ = exec.saturate_ground_search(&mut search, &[root], &[]);
    let (limit, edge, index) = search
        .closure
        .edges()
        .iter()
        .enumerate()
        .find_map(|(i, e)| {
            if let EdgeReason::Packing(w) = e.reason {
                Some((i, *e, w))
            } else {
                None
            }
        })
        .unwrap();
    let literal = exec
        .ctx
        .terms
        .mk_app(Symbol::named("="), [edge.a, edge.b], Sort::Bool);
    let arena = exec.ctx.terms.len();
    let mut emitter = ClosureEmitter::new(&search);
    for _ in 0..16384 {
        emitter.proof.add_assume(root, None);
    }
    assert!(exec
        .emit_ground_packing(&mut emitter, edge, literal, limit, index)
        .is_none());
    assert_eq!(exec.ctx.terms.len(), arena);
    assert_eq!(emitter.proof.steps.len(), 16384);
    let mut emitter = ClosureEmitter::new(&search);
    assert!(
        exec.emit_ground_packing(&mut emitter, edge, literal, 0, index)
            .is_none(),
        "no future alias paths"
    );
    let site = search.packings.witnesses[index].site;
    let root_node = search.packings.sites[site].nodes.pop().unwrap();
    search.packings.sites[site]
        .nodes
        .push(super::super::packing::PackNode::Piece(usize::MAX));
    search.packings.sites[site].nodes.push(root_node);
    let mut emitter = ClosureEmitter::new(&search);
    assert!(
        exec.emit_ground_packing(&mut emitter, edge, literal, limit, index)
            .is_none(),
        "unreachable forged nodes are not emitted"
    );
    let _ = search.packings.sites[site].nodes.pop();
    let _ = search.packings.sites[site].nodes.pop();
    search.packings.sites[site].nodes.push(root_node);
    let extra = super::super::packing::PackPiece {
        source: root,
        high: u32::MAX,
        low: 0,
    };
    search.packings.sites[site].pieces.push(extra);
    let member = search.packings.witnesses[index].members[0];
    search.packings.witnesses[index].members.push(member);
    let mut emitter = ClosureEmitter::new(&search);
    assert!(
        exec.emit_ground_packing(&mut emitter, edge, literal, limit, index)
            .is_none(),
        "unused overflowing pieces are rejected before assembly"
    );
    let _ = search.packings.sites[site].pieces.pop();
    let _ = search.packings.witnesses[index].members.pop();
    search.packings.witnesses[index].members[0].term = edge.b;
    let mut emitter = ClosureEmitter::new(&search);
    assert!(
        exec.emit_ground_packing(&mut emitter, edge, literal, limit, index)
            .is_none(),
        "forged byte witness"
    );
    assert!(!search.packings.current(&exec.ctx.clone()));
    exec.execute_all(&parse("(push 1)(pop 1)").unwrap())
        .unwrap();
    assert!(!search.packings.current(&exec.ctx));
    let mut emitter = ClosureEmitter::new(&search);
    assert!(exec
        .emit_ground_packing(&mut emitter, edge, literal, limit, index)
        .is_none());
}

#[test]
fn packing_forged_index_vectors_and_context_sorts_refuse_before_assembly() {
    use super::super::packing::PackNode;

    for defect in ["indices", "unary-sort", "binary-sort"] {
        let input = fixture(64, 8, 1, true, "");
        let (mut exec, root) = prepared(&input);
        let mut search = GroundSearch::default();
        exec.register_ground_subterms(&mut search.closure, root)
            .unwrap();
        let _ = exec.saturate_ground_search(&mut search, &[root], &[]);
        let (limit, mut edge, witness) = search
            .closure
            .edges()
            .iter()
            .enumerate()
            .find_map(|(i, e)| match e.reason {
                EdgeReason::Packing(w) => Some((i, *e, w)),
                _ => None,
            })
            .unwrap();
        let site_index = search.packings.witnesses[witness].site;
        let site = &mut search.packings.sites[site_index];
        let new_source = if defect != "binary-sort" {
            let (index, child, source) = site
                .nodes
                .iter()
                .enumerate()
                .find_map(|(i, node)| match *node {
                    PackNode::Unary { source, child } => Some((i, child, source)),
                    _ => None,
                })
                .unwrap();
            let TermData::App(_, args) = exec.ctx.terms.get(source) else {
                panic!("extension source")
            };
            let child_source = args[0];
            let forged = exec.ctx.terms.mk_app(
                Symbol::indexed(
                    "zero_extend",
                    if defect == "indices" {
                        vec![56; MAX_NODES + 1]
                    } else {
                        vec![56]
                    },
                ),
                [child_source],
                if defect == "unary-sort" {
                    Sort::Bool
                } else {
                    Sort::bitvec(64)
                },
            );
            site.nodes.truncate(index + 1);
            site.nodes[index] = PackNode::Unary {
                source: forged,
                child,
            };
            site.pieces.truncate(1);
            search.packings.witnesses[witness].members.truncate(1);
            forged
        } else {
            let index = site.nodes.len() - 1;
            let PackNode::Binary {
                source,
                left,
                right,
            } = site.nodes[index]
            else {
                panic!("packing root")
            };
            let TermData::App(symbol, args) = exec.ctx.terms.get(source) else {
                panic!("packing application")
            };
            let symbol = symbol.clone();
            let args = args.clone();
            let forged = exec.ctx.terms.mk_app(symbol, args, Sort::Bool);
            site.nodes[index] = PackNode::Binary {
                source: forged,
                left,
                right,
            };
            forged
        };
        site.source = new_source;
        edge.a = new_source;
        let literal = exec
            .ctx
            .terms
            .mk_app(Symbol::named("="), [edge.a, edge.b], Sort::Bool);
        let arena = exec.ctx.terms.len();
        let mut emitter = ClosureEmitter::new(&search);
        assert!(
            exec.emit_ground_packing(&mut emitter, edge, literal, limit, witness)
                .is_none(),
            "{defect}"
        );
        assert_eq!(exec.ctx.terms.len(), arena, "{defect}");
        assert!(emitter.proof.steps.is_empty(), "{defect}");
    }
}
