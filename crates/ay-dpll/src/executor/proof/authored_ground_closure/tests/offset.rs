// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn word(exec: &mut Executor, name: &str, width: u32) -> TermId {
    exec.ctx.terms.mk_var(name, Sort::bitvec(width))
}

fn number(exec: &mut Executor, value: i64, width: u32) -> TermId {
    exec.ctx.terms.mk_bitvec(BigInt::from(value), width)
}

fn raw(exec: &mut Executor, op: &str, left: TermId, right: TermId, width: u32) -> TermId {
    exec.ctx
        .terms
        .mk_app(Symbol::named(op), [left, right], Sort::bitvec(width))
}

fn unequal(exec: &mut Executor, left: TermId, right: TermId) -> TermId {
    let eq = exec
        .ctx
        .terms
        .mk_app(Symbol::named("="), [left, right], Sort::Bool);
    exec.ctx.terms.mk_not_raw(eq)
}

fn checked_candidate(exec: &mut Executor, root: TermId) -> Proof {
    let candidate = exec
        .early_ground_closure_memory_candidate(root)
        .expect("modular identity candidate");
    assert!(candidate
        .steps
        .iter()
        .all(|step| !matches!(step, ProofStep::Assume(term) if *term != root)));
    assert!(exec
        .check_proof_strict_derivation_with_datatypes(&candidate)
        .unwrap()
        .is_complete());
    assert_eq!(exec.last_proof_raw_original_assertions, [] as [TermId; 0]);
    assert!(exec.last_proof.is_none());
    candidate
}

#[test]
fn modular_offsets_prove_nested_open_addition_and_subtraction() {
    for width in [1, 8, 64, 128] {
        for swapped in [false, true] {
            let mut exec = Executor::new();
            let x = word(&mut exec, "x", width);
            let zero = number(&mut exec, 0, width);
            let five = number(&mut exec, 5, width);
            let three = number(&mut exec, 3, width);
            let two = number(&mut exec, 2, width);
            let inner = raw(&mut exec, "bvadd", x, zero, width);
            let inner = if swapped {
                raw(&mut exec, "bvadd", five, inner, width)
            } else {
                raw(&mut exec, "bvadd", inner, five, width)
            };
            let left = raw(&mut exec, "bvsub", inner, three, width);
            let right = raw(&mut exec, "bvadd", x, two, width);
            let root = unequal(&mut exec, left, right);
            let candidate = checked_candidate(&mut exec, root);
            assert!(intrinsic_count(&candidate, AletheRule::BvOffsetSpinesV1) > 0);
        }
    }
}

#[test]
fn modular_offsets_wrap_and_lift_only_through_justified_operand_classes() {
    for width in [8, 64] {
        let mut exec = Executor::new();
        let x = word(&mut exec, "x", width);
        let alias = word(&mut exec, "alias", width);
        let minus_one = number(&mut exec, -1, width);
        let one = number(&mut exec, 1, width);
        let two = number(&mut exec, 2, width);
        let offset = raw(&mut exec, "bvadd", minus_one, x, width);
        let pin = exec
            .ctx
            .terms
            .mk_app(Symbol::named("="), [alias, offset], Sort::Bool);
        let left = raw(&mut exec, "bvadd", alias, two, width);
        let right = raw(&mut exec, "bvadd", x, one, width);
        let negative = unequal(&mut exec, left, right);
        assert!(exec
            .early_ground_closure_memory_candidate(negative)
            .is_none());
        let root = exec
            .ctx
            .terms
            .mk_app(Symbol::named("and"), [pin, negative], Sort::Bool);
        let candidate = checked_candidate(&mut exec, root);
        assert!(
            lemma_count(&candidate, |kind, _| matches!(
                kind,
                TheoryLemmaKind::EufCongruent
            )) > 0
        );
    }
}

#[test]
fn modular_offsets_keep_wrong_bases_offsets_widths_and_heads_separate() {
    for wrong_base in [false, true] {
        let mut exec = Executor::new();
        let x = word(&mut exec, "x", 8);
        let y = word(&mut exec, "y", 8);
        let five = number(&mut exec, 5, 8);
        let three = number(&mut exec, 3, 8);
        let wrong = number(&mut exec, if wrong_base { 8 } else { 9 }, 8);
        let left = raw(&mut exec, "bvadd", x, five, 8);
        let left = raw(&mut exec, "bvadd", left, three, 8);
        let right = raw(&mut exec, "bvadd", if wrong_base { y } else { x }, wrong, 8);
        let root = unequal(&mut exec, left, right);
        assert!(exec.early_ground_closure_memory_candidate(root).is_none());
    }
    let mut exec = Executor::new();
    let x = word(&mut exec, "x", 8);
    let wide = number(&mut exec, 0, 16);
    let zero = number(&mut exec, 0, 8);
    for (head, constant) in [("bvadd", wide), ("private_bvadd", zero)] {
        let term = raw(&mut exec, head, x, constant, 8);
        let mut closure = GroundClosure::default();
        exec.register_ground_subterms(&mut closure, term).unwrap();
        exec.add_ground_modular_offset_identity_edges(
            &mut closure,
            &mut 512,
            &mut SharedGroundWork::new(MAX_NODES * MAX_ROUNDS),
        )
        .unwrap();
        assert!(!closure.same_class(term, x));
        assert_eq!(closure.edges(), []);
    }
    let malformed = raw(&mut exec, "bvsub", wide, zero, 8);
    let term = raw(&mut exec, "bvadd", malformed, zero, 8);
    let mut closure = GroundClosure::default();
    exec.register_ground_subterms(&mut closure, term).unwrap();
    exec.add_ground_modular_offset_identity_edges(
        &mut closure,
        &mut 512,
        &mut SharedGroundWork::new(MAX_NODES * MAX_ROUNDS),
    )
    .unwrap();
    assert!(
        closure.edges().is_empty(),
        "a malformed nested cancellation cannot merge widths"
    );
}

#[test]
fn modular_offset_search_preserves_shared_work_and_proposal_limits() {
    let mut exec = Executor::new();
    let x = word(&mut exec, "x", 64);
    let zero = number(&mut exec, 0, 64);
    let term = raw(&mut exec, "bvadd", x, zero, 64);
    let mut closure = GroundClosure::default();
    exec.register_ground_subterms(&mut closure, term).unwrap();
    assert!(exec
        .add_ground_modular_offset_identity_edges(
            &mut closure,
            &mut 1,
            &mut SharedGroundWork::new(0)
        )
        .is_none());
    assert_eq!(closure.edges(), []);
    let mut work = SharedGroundWork::new(MAX_NODES * MAX_ROUNDS);
    exec.add_ground_modular_offset_identity_edges(&mut closure, &mut 0, &mut work)
        .unwrap();
    assert_eq!(work.remaining(), MAX_NODES * MAX_ROUNDS);
    assert_eq!(closure.edges(), []);
    let mut proposals = 1;
    exec.add_ground_modular_offset_identity_edges(&mut closure, &mut proposals, &mut work)
        .unwrap();
    assert_eq!(proposals, 0);
    assert!(closure.same_class(term, x));
    assert!(work.remaining() < MAX_NODES * MAX_ROUNDS);
}

#[test]
fn modular_offset_spine_refuses_before_constructor_allocation_when_work_runs_out() {
    let mut exec = Executor::new();
    let x = word(&mut exec, "x", 64);
    let one = number(&mut exec, 1, 64);
    let inner = raw(&mut exec, "bvadd", x, one, 64);
    let outer = raw(&mut exec, "bvadd", inner, one, 64);
    let mut closure = GroundClosure::default();
    exec.register_ground_subterms(&mut closure, outer).unwrap();
    // The map scan and first site fit, as does the first spine node. The
    // preflight then runs out while following `inner` to `x`, before the
    // constructor could create the new literal two or `(bvadd x two)`.
    let mut work = SharedGroundWork::new(closure.nodes().len() + 3);
    let mut proposals = 1;
    let arena_len = exec.ctx.terms.len();
    assert!(exec
        .add_ground_modular_offset_identity_edges(&mut closure, &mut proposals, &mut work)
        .is_none());
    assert_eq!(work.remaining(), 0);
    assert_eq!(proposals, 1);
    assert_eq!(exec.ctx.terms.len(), arena_len);
    assert_eq!(closure.edges(), []);
    assert_eq!(exec.last_proof_raw_original_assertions, [] as [TermId; 0]);
}

#[test]
fn modular_offset_stop_prevents_identity_merges() {
    let mut exec = Executor::new();
    let x = word(&mut exec, "x", 64);
    let zero = number(&mut exec, 0, 64);
    let term = raw(&mut exec, "bvadd", x, zero, 64);
    let mut closure = GroundClosure::default();
    exec.register_ground_subterms(&mut closure, term).unwrap();
    exec.set_interrupt(std::sync::Arc::new(std::sync::atomic::AtomicBool::new(
        true,
    )));
    assert!(exec
        .add_ground_modular_offset_identity_edges(
            &mut closure,
            &mut 1,
            &mut SharedGroundWork::new(MAX_NODES * MAX_ROUNDS),
        )
        .is_none());
    assert_eq!(closure.edges(), []);
    assert_eq!(exec.last_proof_raw_original_assertions, [] as [TermId; 0]);
    assert!(exec.last_proof().is_none());
}

#[test]
fn modular_offset_alias_scope_does_not_survive_pop() {
    let source = r#"
(set-option :produce-proofs true)
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(declare-const alias (_ BitVec 8))
(assert (not (= (bvadd alias #x02) (bvadd x #x01))))
(push 1)
(assert (= alias (bvadd x #xff)))
(check-sat)
"#;
    let mut exec = solved(source, "unsat");
    exec.check_proof_strict_with_datatypes(exec.last_proof().expect("source proof"))
        .unwrap();
    let outputs = exec
        .execute_all(&parse("(pop 1)(check-sat)").unwrap())
        .unwrap();
    assert_eq!(outputs, ["sat"]);
    assert!(exec.last_proof().is_none());
}

#[test]
fn original_memory_offset_stage_retains_the_actual_connected_frontier() {
    const ORIGINAL: &str = include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/src/executor/proof_original_e1_exit0.smt2"
    ));
    let mut exec = Executor::new();
    for command in parse(ORIGINAL).unwrap() {
        if !matches!(command, Command::CheckSat | Command::Exit) {
            exec.execute_all(&[command]).unwrap();
        }
    }
    let source = exec.ctx.assertions_parsed()[0].clone();
    let root = exec
        .raw_intern_shared_ground_memory_surface(&source)
        .unwrap();
    let mut search = GroundSearch::default();
    exec.register_ground_subterms(&mut search.closure, root)
        .unwrap();
    let store_keys: Vec<_> = search
        .closure
        .nodes()
        .iter()
        .filter_map(|&term| store_parts_local(&exec.ctx.terms, term).map(|(_, key, _)| key))
        .collect();
    let read_keys: Vec<_> = search
        .closure
        .nodes()
        .iter()
        .filter_map(|&term| {
            let (array, key) = select_parts_local(&exec.ctx.terms, term)?;
            store_parts_local(&exec.ctx.terms, array).map(|_| key)
        })
        .collect();
    let before = read_keys
        .iter()
        .filter(|&&key| store_keys.contains(&key))
        .count();
    let conflict = exec.saturate_ground_search(&mut search, &[root], &[]);
    println!("original memory modular-offset stage: conflict={conflict:?} nodes={} edges={} facts={} probes_remaining={}", search.closure.nodes().len(), search.closure.edges().len(), search.facts.facts().len(), search.probes);
    let after = read_keys
        .iter()
        .filter(|&&key| {
            store_keys
                .iter()
                .any(|&written| search.closure.same_class(key, written))
        })
        .count();
    println!(
        "original memory store/read key alignment: {before} -> {after} of {}",
        read_keys.len()
    );
    let direct_reads = search
        .closure
        .edges()
        .iter()
        .filter(|edge| matches!(edge.reason, EdgeReason::ReadChain(_)))
        .count();
    let skipped = search
        .read_chains
        .witnesses
        .iter()
        .map(|witness| witness.skipped.len())
        .sum::<usize>();
    println!("original memory direct ROW stage: read_edges={direct_reads} witnesses={} unique_skip_occurrences={skipped}", search.read_chains.witnesses.len());
    let packed = search
        .closure
        .edges()
        .iter()
        .filter(|edge| matches!(edge.reason, EdgeReason::Packing(_)))
        .count();
    println!(
        "original memory packing stage: sites={} witnesses={} edges={packed}",
        search.packings.sites.len(),
        search.packings.witnesses.len()
    );
    let conflict = conflict.expect("the unchanged search has the original goal conflict");
    let candidate = exec
        .emit_ground_closure_refutation(&search, conflict)
        .expect("bounded checked emission completes without another allowance");
    {
        println!(
            "original memory packing candidate steps={}",
            candidate.steps.len()
        );
        assert_eq!(intrinsic_count(&candidate, AletheRule::BvReconstructV1), 10);
        assert!(intrinsic_count(&candidate, AletheRule::BvOffsetSpinesV1) > 0);
        assert!(candidate
            .steps
            .iter()
            .all(|step| !matches!(step, ProofStep::Assume(term) if *term != root)));
        let quality = exec
            .check_proof_strict_derivation_with_datatypes(&candidate)
            .expect("separately checked intrinsics fit the original unchanged envelope");
        assert!(quality.is_complete());
        let mut work = 0usize;
        let mut bytes = 0usize;
        ay_proof::check_proof_strict_with_context_and_progress(
            &candidate,
            &exec.ctx.terms,
            None,
            None,
            Some(&[root]),
            &mut |w, b| {
                work = work.saturating_add(w);
                bytes = bytes.saturating_add(b);
                work <= 350_000_000 && bytes <= 1_342_177_280
            },
        )
        .expect("exact native source and one shared unchanged aggregate");
        println!(
            "original memory packing strict positive: steps={} work={work} admission_bytes={bytes}",
            candidate.steps.len()
        );
        let mut redundant = candidate.clone();
        for step in &mut redundant.steps {
            if let ProofStep::Step {
                rule: AletheRule::AndNeg,
                clause,
                args,
                ..
            } = step
            {
                assert_eq!(args.as_slice(), []);
                args.push(clause[0]);
            }
        }
        // The incoming argument-bearing identity class now admits this
        // representation too. It is distinct from the producer's no-arg
        // General route, and must still replay the same original assertion.
        assert!(exec
            .check_proof_strict_derivation_with_datatypes(&redundant)
            .unwrap()
            .is_complete());
        ay_proof::check_proof_strict_with_context(
            &redundant,
            &exec.ctx.terms,
            None,
            None,
            Some(&[root]),
        )
        .unwrap();
        if let Ok(directory) = std::env::var("AY_CHECKED_GROUND_EMIT_ARTIFACT_DIR") {
            std::fs::create_dir_all(&directory).unwrap();
            let negative = exec.ctx.terms.mk_not_raw(root);
            exec.last_proof_term_overrides = exec
                .checked_ground_literal_spellings(root, negative, &candidate)
                .expect("original checked presentation is not stopped");
            let overrides = exec.proof_export_term_overrides();
            let surfaces = exec.authored_export_surfaces();
            let text = exec
                .in_alethe_dialect(|| {
                    ay_proof::try_export_alethe_with_authored_surfaces(
                        &candidate,
                        &exec.ctx.terms,
                        &[root],
                        overrides.as_ref(),
                        surfaces.channels(),
                        None,
                    )
                })
                .expect("diagnostic export retains any real wire loss");
            packing::retain("original-e1-native", ORIGINAL, Some(&text));
            let report = serde_json::json!({"steps":candidate.steps.len(),"strict_native":true,"exact_source":true,"work":work,"admission_bytes":bytes,"reconstruct_units":intrinsic_count(&candidate,AletheRule::BvReconstructV1),"offset_units":intrinsic_count(&candidate,AletheRule::BvOffsetSpinesV1),"wire_holes":text.matches(":rule hole").count(),"no_public_full_proof_claim":true});
            std::fs::write(
                std::path::Path::new(&directory).join("original-native.json"),
                serde_json::to_vec_pretty(&report).unwrap(),
            )
            .unwrap();
        }
    }
    assert!(
        direct_reads > 0,
        "the unchanged source gains direct, proof-backed read equalities"
    );
    assert!(
        after > before,
        "the source's open offsets acquire justified equalities"
    );
    assert!(search
        .closure
        .edges()
        .iter()
        .any(|edge| edge.reason == EdgeReason::ModularOffset));
    assert!(search.closure.nodes().len() <= MAX_NODES);
    assert!(search.closure.edges().len() <= MAX_EDGES);
    let negative = exec.ctx.terms.mk_not_raw(root);
    let mut direct = Proof::new();
    let premise = direct.add_assume(root, None);
    let lemma =
        direct.add_theory_lemma_with_kind("bv", vec![negative], TheoryLemmaKind::BvBitBlast);
    direct.add_resolution(Vec::new(), root, premise, lemma);
    let refusal = exec
        .check_proof_strict_derivation_with_datatypes(&direct)
        .expect_err("the unchanged eighty-store source still exceeds sparse's hard chain bound");
    assert!(refusal
        .to_string()
        .contains("sparse array store-chain budget exceeded"));
    println!("original memory direct strict refusal: {refusal}");
    assert_eq!(exec.last_proof_raw_original_assertions, [] as [TermId; 0]);
    assert!(exec.last_proof().is_none());
}

#[test]
fn modular_offsets_normalize_closed_addends_inside_open_addresses() {
    for width in [8, 64] {
        let mut exec = Executor::new();
        let x = word(&mut exec, "x", width);
        let one = number(&mut exec, 1, width);
        let minus_eight = number(&mut exec, -8, width);
        let minus_seven = number(&mut exec, -7, width);
        let closed = raw(&mut exec, "bvadd", one, minus_eight, width);
        let left = raw(&mut exec, "bvadd", closed, x, width);
        let right = raw(&mut exec, "bvadd", x, minus_seven, width);
        let root = unequal(&mut exec, left, right);
        checked_candidate(&mut exec, root);
    }
}

#[test]
fn modular_offsets_closed_addends_still_need_the_base_alias_premise() {
    for width in [8, 64] {
        let mut exec = Executor::new();
        let x = word(&mut exec, "x", width);
        let alias = word(&mut exec, "alias", width);
        let forty_eight = number(&mut exec, 48, width);
        let eight = number(&mut exec, 8, width);
        let eighty = number(&mut exec, 80, width);
        let minus_twenty_four = number(&mut exec, -24, width);
        let closed = raw(&mut exec, "bvadd", forty_eight, eight, width);
        let left = raw(&mut exec, "bvadd", closed, alias, width);
        let right = raw(&mut exec, "bvadd", x, minus_twenty_four, width);
        let negative = unequal(&mut exec, left, right);
        assert!(exec
            .early_ground_closure_memory_candidate(negative)
            .is_none());
        let base = raw(&mut exec, "bvsub", x, eighty, width);
        let pin = exec
            .ctx
            .terms
            .mk_app(Symbol::named("="), [alias, base], Sort::Bool);
        let root = exec
            .ctx
            .terms
            .mk_app(Symbol::named("and"), [pin, negative], Sort::Bool);
        let candidate = checked_candidate(&mut exec, root);
        assert!(
            lemma_count(&candidate, |kind, _| matches!(
                kind,
                TheoryLemmaKind::EufCongruent
            )) > 0
        );
    }
}
