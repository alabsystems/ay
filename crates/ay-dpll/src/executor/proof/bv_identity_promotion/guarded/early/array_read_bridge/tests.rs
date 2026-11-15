// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

pub(super) fn loaded(source: &str) -> Executor {
    let mut executor = Executor::new();
    for command in ay_frontend::parse(source).unwrap() {
        if !matches!(
            command,
            ay_frontend::Command::CheckSat | ay_frontend::Command::Exit
        ) {
            executor.execute(&command).unwrap();
        }
    }
    executor
}

fn eighty_array() -> String {
    let mut array = "memory".to_string();
    for index in 0..80 {
        array = format!("(store {array} (bvadd base (_ bv{index} 64)) (_ bv{index} 8))");
    }
    array
}

pub(super) fn eighty_stores(expected: u8) -> String {
    let array = eighty_array();
    format!("(declare-const memory (Array (_ BitVec 64) (_ BitVec 8)))(declare-const base (_ BitVec 64))(assert (not (= (select {array} (bvadd (bvsub base (_ bv80 64)) (_ bv80 64))) (_ bv{expected} 8))))")
}

fn nested_reversed_binding(expected: u8) -> String {
    let array = eighty_array();
    format!("(declare-const memory (Array (_ BitVec 64) (_ BitVec 8)))(declare-const base (_ BitVec 64))(declare-const resume (_ BitVec 64))(assert (and (and true (= (bvadd base (_ bv80 64)) resume)) (and (= (select memory base) (_ bv42 8)) (not (= (bvadd (select {array} base) (select memory (bvsub resume (_ bv80 64)))) (_ bv{expected} 8))))))")
}

#[test]
fn nested_reversed_source_binding_is_derived_and_wrong_value_retains_counterexample() {
    for expected in [42, 43] {
        let mut executor = loaded(&nested_reversed_binding(expected));
        let root = raw_root(&mut executor);
        let proof = executor
            .early_array_read_memory_candidate(root)
            .expect("bounded binding candidate");
        assert!(
            proof.steps.iter().any(|step| matches!(
                step,
                ay_core::ProofStep::Step {
                    rule: AletheRule::Symm,
                    ..
                }
            )),
            "the reversed source equality must actually enter SourceBinding"
        );
        assert_eq!(
            proof
                .steps
                .iter()
                .filter(|step| matches!(step, ay_core::ProofStep::Assume(..)))
                .count(),
            1
        );
        let result = executor.check_proof_strict_derivation_with_datatypes(&proof);
        println!("NESTED_REVERSED_BINDING expected={expected} result={result:?}");
        if expected == 42 {
            assert!(result.unwrap().is_complete());
        } else {
            assert!(matches!(
                result,
                Err(ay_proof::ProofCheckError::InvalidTheoryLemma {
                    step: ProofId(1),
                    ..
                })
            ));
        }
    }
}

pub(super) fn raw_root(executor: &mut Executor) -> TermId {
    let parsed = executor.ctx.assertions_parsed()[0].clone();
    executor
        .raw_intern_shared_ground_memory_surface(&parsed)
        .unwrap()
}

#[test]
fn eighty_store_demanded_read_is_derived_without_fresh_memory_assumptions() {
    let mut executor = loaded(&eighty_stores(0));
    let root = raw_root(&mut executor);
    let proof = executor
        .early_array_read_memory_candidate(root)
        .expect("bounded row derivation");
    assert_eq!(
        proof
            .steps
            .iter()
            .filter_map(|step| match step {
                ay_core::ProofStep::Assume(term) => Some(*term),
                _ => None,
            })
            .collect::<Vec<_>>(),
        [root]
    );
    assert!(proof.steps.iter().any(|step| matches!(
        step,
        ay_core::ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::ArrayRowChain,
            ..
        }
    )));
    assert!(executor
        .check_proof_strict_derivation_with_datatypes(&proof)
        .unwrap()
        .is_complete());
}

#[test]
fn wrong_eighty_store_read_value_does_not_acquire_a_refutation() {
    let mut executor = loaded(&eighty_stores(1));
    let root = raw_root(&mut executor);
    let proof = executor
        .early_array_read_memory_candidate(root)
        .expect("candidate is not authority");
    let error = executor
        .check_proof_strict_derivation_with_datatypes(&proof)
        .unwrap_err();
    println!("WRONG_VALUE_STRICT_REFUSAL {error:?}");
    assert!(matches!(
        error,
        ay_proof::ProofCheckError::InvalidTheoryLemma {
            step: ProofId(1),
            ..
        }
    ));
    assert!(executor.last_proof.is_none());
    assert!(executor.last_proof_raw_original_assertions.is_empty());
}

#[test]
fn original_e1_demanded_reads_leave_only_the_original_source_assume() {
    let _flags = ay_core::misc_test_override::set(ay_core::MiscCliFlags {
        probe_strict_check: true,
        ..ay_core::misc_cli_flags().clone()
    });
    let source = include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/fixtures/external_codegen_e1_static_frame_exit0.smt2"
    ));
    let mut executor = loaded(source);
    executor.set_timeout(Some(std::time::Duration::from_secs(30)));
    executor.set_memory_limit(Some(8192 * 1024 * 1024));
    let root = raw_root(&mut executor);
    let proof = executor
        .early_array_read_memory_candidate(root)
        .expect("original demanded-read candidate");
    assert_eq!(
        proof
            .steps
            .iter()
            .filter_map(|step| match step {
                ay_core::ProofStep::Assume(term) => Some(*term),
                _ => None,
            })
            .collect::<Vec<_>>(),
        [root]
    );
    let quality = executor.check_proof_strict_derivation_with_datatypes(&proof);
    let bv_lemmas = proof
        .steps
        .iter()
        .filter(|step| {
            matches!(
                step,
                ay_core::ProofStep::TheoryLemma {
                    kind: TheoryLemmaKind::BvBitBlast,
                    ..
                }
            )
        })
        .count();
    assert_eq!(bv_lemmas, 1);
    println!(
        "E1_ROW_BRIDGE_NATIVE steps={} bv_lemmas={bv_lemmas} quality={quality:?}",
        proof.steps.len()
    );
    assert!(
        quality.unwrap().is_complete(),
        "only full strict replay can qualify this candidate"
    );
}

#[test]
fn generated_group_must_keep_actual_builtin_ownership_and_result_sort() {
    let query = eighty_stores(0).replace(
        "(bvadd (bvsub base (_ bv80 64)) (_ bv80 64))",
        "(bvadd base (_ bv0 64))",
    );
    let mut group_refusals = 0;
    for declaration in [
        "(declare-fun and (Bool Bool) Bool)",
        "(define-fun and ((a Bool) (b Bool)) Int 0)",
        "(define-fun bvsub ((a (_ BitVec 64)) (b (_ BitVec 64))) (_ BitVec 64) a)",
    ] {
        let source = format!("{declaration}{query}");
        let mut executor = Executor::new();
        let mut language_refused = false;
        for command in ay_frontend::parse(&source).unwrap() {
            if executor.execute(&command).is_err() {
                language_refused = true;
                break;
            }
        }
        if language_refused {
            println!("GROUP_OWNERSHIP language_refused {declaration}");
            continue;
        }
        let root = raw_root(&mut executor);
        assert!(executor.early_array_read_memory_candidate(root).is_none());
        assert!(executor.last_proof.is_none());
        group_refusals += 1;
        println!("GROUP_OWNERSHIP generated_group_refused {declaration}");
    }
    assert!(
        group_refusals > 0,
        "exercise an actual accepted declaration context"
    );
}

#[test]
fn demanded_read_bridge_obeys_the_original_live_stop() {
    use std::sync::{atomic::AtomicBool, Arc};
    let mut executor = loaded(&eighty_stores(0));
    let root = raw_root(&mut executor);
    executor.set_interrupt(Arc::new(AtomicBool::new(true)));
    assert!(executor.early_array_read_memory_candidate(root).is_none());
    assert!(executor.last_proof.is_none());
}

fn source_budget_fixture(leaves: usize) -> (Executor, TermId) {
    let mut executor = Executor::new();
    let variables: Vec<_> = (0..leaves)
        .map(|index| executor.ctx.terms.mk_var(format!("p{index}"), Sort::Bool))
        .collect();
    let groups: Vec<_> = variables
        .chunks(128)
        .map(|chunk| {
            executor
                .ctx
                .terms
                .mk_app(Symbol::named("and"), chunk, Sort::Bool)
        })
        .collect();
    let mut root = executor
        .ctx
        .terms
        .mk_app(Symbol::named("and"), &groups, Sort::Bool);
    for _ in 0..80 {
        root = executor.ctx.terms.mk_not_raw(root);
    }
    (executor, root)
}

#[test]
fn source_census_counts_pending_parents_at_the_exact_boundary() {
    for (leaves, expected) in [(1951, true), (1952, false)] {
        let (mut executor, root) = source_budget_fixture(leaves);
        let stop = || false;
        let read_hints = ReadHints::empty(&executor.ctx);
        let mut builder = ReadBridge {
            executor: &mut executor,
            proof: Proof::new(),
            memo: HashMap::default(),
            arithmetic: HashMap::default(),
            source_seen: HashSet::default(),
            rewrite_seen: HashSet::default(),
            side_seen: HashSet::default(),
            side_literals: Vec::new(),
            side_unique: HashSet::default(),
            read_hints,
            plan_memo: HashMap::default(),
            address_norms: HashMap::default(),
            visits: 0,
            stop: &stop,
        };
        assert_eq!(builder.collect(root, 0).is_some(), expected);
        assert_eq!(builder.source_seen.len(), MAX_TERMS);
        if expected {
            assert_eq!(builder.rewrite(root, 0), Some((root, None)));
            assert_eq!(builder.memo.len(), MAX_TERMS);
            assert_eq!(builder.rewrite_seen.len(), MAX_TERMS);
        } else {
            assert!(builder.memo.is_empty());
        }
    }
}

#[test]
fn source_binding_reserves_the_complete_and_path_before_appending() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::bitvec(64));
    let y = executor.ctx.terms.mk_var("y", Sort::bitvec(64));
    let one = executor.ctx.terms.mk_bitvec(1.into(), 64);
    let rhs = executor
        .ctx
        .terms
        .mk_app(Symbol::named("bvadd"), [y, one], Sort::bitvec(64));
    let reversed = executor
        .ctx
        .terms
        .mk_app(Symbol::named("="), [rhs, x], Sort::Bool);
    let other = executor
        .ctx
        .terms
        .mk_app(Symbol::named("="), [x, y], Sort::Bool);
    let inner = executor
        .ctx
        .terms
        .mk_app(Symbol::named("and"), [reversed, other], Sort::Bool);
    let truth = executor.ctx.terms.mk_bool(true);
    let root = executor
        .ctx
        .terms
        .mk_app(Symbol::named("and"), [truth, inner], Sort::Bool);
    let stop = || false;
    let read_hints = ReadHints::empty(&executor.ctx);
    let mut builder = ReadBridge {
        executor: &mut executor,
        proof: Proof::new(),
        memo: HashMap::default(),
        arithmetic: HashMap::default(),
        source_seen: HashSet::default(),
        rewrite_seen: HashSet::default(),
        side_seen: HashSet::default(),
        side_literals: Vec::new(),
        side_unique: HashSet::default(),
        read_hints,
        plan_memo: HashMap::default(),
        address_norms: HashMap::default(),
        visits: 0,
        stop: &stop,
    };
    builder.collect(root, 0).unwrap();
    let binding = builder.source_address_binding(root).unwrap().unwrap();
    let target = builder.substitution_image(root, &binding, None).unwrap().0;
    // Capacity-only fixture; no semantic acceptance is claimed for this
    // synthetic prefix. The actual nested/reversed path needs five steps.
    builder
        .proof
        .steps
        .resize(MAX_STEPS - 4, ay_core::ProofStep::Assume(root));
    let before = builder.proof.steps.len();
    assert!(builder
        .derive_substitution(root, target, ProofId(0), &binding)
        .is_none());
    assert_eq!(builder.proof.steps.len(), before);
}

#[test]
fn residual_reads_use_checked_key_congruence_and_keep_wrong_value_or_offset_models() {
    for (expected, memory_offset, valid) in [(43u8, 1u8, true), (44, 1, false), (43, 2, false)] {
        let array = eighty_array();
        let source = format!("(declare-const memory (Array (_ BitVec 64) (_ BitVec 8)))(declare-const base (_ BitVec 64))(assert (and (= (select memory (bvadd base (_ bv{memory_offset} 64))) (_ bv42 8)) (not (= (bvadd (select {array} (bvadd base (_ bv1 64))) (select memory (bvadd (bvadd base (_ bv1 64)) (_ bv0 64)))) (_ bv{expected} 8)))))");
        let mut executor = loaded(&source);
        let root = raw_root(&mut executor);
        let proof = executor
            .early_array_read_memory_candidate(root)
            .expect("candidate remains independently checked");
        let read_congruences = proof.steps.iter().filter(|step| {
            let ay_core::ProofStep::Step {rule:AletheRule::Cong,clause,..}=step else {return false;};
            let [eq]=clause.as_slice() else{return false;};
            let TermData::App(_,sides)=executor.ctx.terms.get(*eq) else{return false;};
            sides.len()==2 && sides.iter().all(|&side| matches!(executor.ctx.terms.get(side),TermData::App(Symbol::Named(head),args) if head=="select" && args.len()==2 && matches!(executor.ctx.terms.get(args[0]),TermData::Var(..))))
        }).count();
        let result = executor.check_proof_strict_derivation_with_datatypes(&proof);
        println!("RESIDUAL_READ_IMAGE expected={expected} memory_offset={memory_offset} read_congruences={read_congruences} result={result:?}");
        if valid {
            assert!(
                read_congruences > 0,
                "must enter actual residual-read transport"
            );
            assert!(result.unwrap().is_complete());
        } else {
            assert!(matches!(
                result,
                Err(ay_proof::ProofCheckError::InvalidTheoryLemma {
                    step: ProofId(1),
                    ..
                })
            ));
        }
    }
}

#[test]
fn original_e1_derived_joint_bv_obligation_has_a_bounded_complete_wire_proof() {
    use std::io::Write;
    let original = include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/fixtures/external_codegen_e1_static_frame_exit0.smt2"
    ));
    let mut executor = loaded(original);
    executor.set_timeout(Some(std::time::Duration::from_secs(30)));
    executor.set_memory_limit(Some(8192 * 1024 * 1024));
    let root = raw_root(&mut executor);
    let derivation = executor
        .early_array_read_memory_candidate(root)
        .expect("actual E1 producer");
    assert!(executor
        .check_proof_strict_derivation_with_datatypes(&derivation)
        .unwrap()
        .is_complete());
    let ay_core::ProofStep::TheoryLemma {
        kind: TheoryLemmaKind::BvBitBlast,
        clause,
        ..
    } = &derivation.steps[1]
    else {
        panic!("one joint BV obligation");
    };
    let [joint] = clause.as_slice() else {
        panic!("joint unit");
    };
    let joint = *joint;
    let assumption = executor.ctx.terms.mk_not_raw(joint);
    let mut proof = Proof::new();
    let premise = proof.add_assume(assumption, None);
    let lemma = proof.add_theory_lemma_with_kind("bv", vec![joint], TheoryLemmaKind::BvBitBlast);
    proof.add_resolution(vec![], assumption, premise, lemma);
    ay_proof::check_proof_strict_with_context(
        &proof,
        &executor.ctx.terms,
        None,
        None,
        Some(&[assumption]),
    )
    .unwrap();
    struct Bounded(Vec<u8>);
    impl Write for Bounded {
        fn write(&mut self, bytes: &[u8]) -> std::io::Result<usize> {
            if self
                .0
                .len()
                .checked_add(bytes.len())
                .is_none_or(|n| n > 16 * 1024 * 1024)
            {
                return Err(std::io::Error::other(
                    "unchanged16MiB diagnostic capture cap",
                ));
            }
            self.0.extend_from_slice(bytes);
            Ok(bytes.len())
        }
        fn flush(&mut self) -> std::io::Result<()> {
            Ok(())
        }
    }
    let mut output = Bounded(Vec::new());
    let result = ay_proof::try_export_alethe_with_problem_scope_overrides_and_budget_to(
        &mut output,
        &proof,
        &executor.ctx.terms,
        &[assumption],
        None,
        None,
    );
    println!(
        "E1_DERIVED_BV_COMPONENT proof_bytes={} export={result:?}",
        output.0.len()
    );
    let source = ay_proof::format_term_alethe(&executor.ctx.terms, assumption);
    let prelude = original.split_once("(assert ").unwrap().0;
    let problem = format!("{prelude}(assert {source})\n(check-sat)\n");
    if let Some(path) = std::env::var_os("AY_E1_BV_COMPONENT_ARTIFACT_DIR") {
        let path = std::path::PathBuf::from(path);
        assert!(path.is_absolute());
        std::fs::create_dir(&path).unwrap();
        for (name, bytes) in [
            ("original-derived-component.smt2", problem.as_bytes()),
            ("proof.alethe", output.0.as_slice()),
        ] {
            let mut file = std::fs::OpenOptions::new()
                .write(true)
                .create_new(true)
                .open(path.join(name))
                .unwrap();
            file.write_all(bytes).unwrap();
        }
        std::fs::write(path.join("result.txt"), format!("{result:?}\n")).unwrap();
        if result.is_ok() {
            let certificate=serde_json::to_vec(&serde_json::json!({"type":"alethe_certificate","version":"1.0","problem":problem,"proof":String::from_utf8(output.0.clone()).unwrap()})).unwrap();
            // The bounded writer limits Alethe bytes. JSON additionally
            // transports the independently bounded source and escapes text;
            // record its real size without inventing a second proof cap.
            println!(
                "E1_DERIVED_BV_COMPONENT certificate_json_bytes={}",
                certificate.len()
            );
            std::fs::write(path.join("certificate.json"), certificate).unwrap();
        }
    }
    result.expect("native truth is insufficient without a complete bounded wire derivation");
    let text = String::from_utf8(output.0).unwrap();
    assert!(!text.contains(":rule hole") && !text.contains(":rule trust"));
}
