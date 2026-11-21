// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::time::Duration;
use std::{
    path::Path,
    process::{Command, Stdio},
};
use wait_timeout::ChildExt as _;

use crate::api::*;

fn group() -> Vec<DatatypeSort> {
    vec![
        DatatypeSort::new(
            "BatchTree",
            vec![
                DatatypeConstructor::new(
                    "batch_leaf",
                    vec![DatatypeField::new("batch_value", Sort::Int)],
                ),
                DatatypeConstructor::new(
                    "batch_node",
                    vec![DatatypeField::new(
                        "batch_children",
                        Sort::Uninterpreted("BatchForest".into()),
                    )],
                ),
            ],
        ),
        DatatypeSort::new(
            "BatchForest",
            vec![
                DatatypeConstructor::unit("batch_nil"),
                DatatypeConstructor::new(
                    "batch_cons",
                    vec![
                        DatatypeField::new("batch_head", Sort::Uninterpreted("BatchTree".into())),
                        DatatypeField::new("batch_tail", Sort::Uninterpreted("BatchForest".into())),
                    ],
                ),
            ],
        ),
    ]
}

fn budget(work: usize, storage: usize) -> NativeDatatypeBatchBudget {
    NativeDatatypeBatchBudget::new(NativeDatatypeBatchLimits::new(work, storage, 128))
}

fn checker_run(
    binary: &Path,
    args: &[&std::ffi::OsStr],
    directory: &Path,
    tag: &str,
) -> (std::process::ExitStatus, String) {
    let output = directory.join(format!("{tag}.stdout"));
    let errors = directory.join(format!("{tag}.stderr"));
    let mut child = Command::new(binary)
        .args(args)
        .stdin(Stdio::null())
        .stdout(std::fs::File::create(&output).unwrap())
        .stderr(std::fs::File::create(&errors).unwrap())
        .spawn()
        .expect("required pinned Carcara");
    let Some(status) = child.wait_timeout(Duration::from_secs(5)).unwrap() else {
        child.kill().unwrap();
        child.wait().unwrap();
        panic!("pinned Carcara {tag} exceeded five seconds");
    };
    assert!(std::fs::metadata(&output).unwrap().len() <= 1024 * 1024);
    assert!(std::fs::metadata(&errors).unwrap().len() <= 1024 * 1024);
    (
        status,
        format!(
            "{}\n{}",
            std::fs::read_to_string(output).unwrap(),
            std::fs::read_to_string(errors).unwrap()
        ),
    )
}

pub(super) fn check_whole_paired_document(problem: &str, proof: &str, surface: &CarcaraSurface) {
    use sha2::{Digest, Sha256};
    let binary = std::env::split_paths(&std::env::var_os("PATH").unwrap())
        .map(|directory| directory.join("carcara"))
        .find(|path| path.is_file())
        .expect("pinned Carcara is required")
        .canonicalize()
        .unwrap();
    let directory = tempfile::tempdir().unwrap();
    let before = Sha256::digest(std::fs::read(&binary).unwrap());
    let (status, version) = checker_run(
        &binary,
        &[std::ffi::OsStr::new("--version")],
        directory.path(),
        "version",
    );
    assert!(status.success(), "{status} {version}");
    assert!(
        version.contains("carcara 1.1.0") && version.contains("9a352ee"),
        "{version}"
    );
    let problem_path = directory.path().join("query.smt2");
    let proof_path = directory.path().join("proof.alethe");
    std::fs::write(&problem_path, problem).unwrap();
    std::fs::write(&proof_path, proof).unwrap();
    ay_core::pinned_carcara::pinned_carcara_can_judge(problem, proof).unwrap();
    let (status, output) = checker_run(
        &binary,
        &[
            std::ffi::OsStr::new("check"),
            std::ffi::OsStr::new("--"),
            proof_path.as_os_str(),
            problem_path.as_os_str(),
        ],
        directory.path(),
        "positive",
    );
    let clean_dialect = matches!(surface, CarcaraSurface::CleanDialect { .. });
    if clean_dialect {
        assert!(
            !status.success() && output.contains("unknown rule"),
            "{output}"
        );
    } else {
        assert!(surface.is_supported(), "{surface}");
        assert!(
            status.success() && output.lines().any(|line| line == "valid"),
            "{output}\n{proof}"
        );
    }
    let mut forged = proof.to_owned();
    let final_clause = forged
        .rfind("(cl)")
        .expect("native proof has an empty conclusion");
    let rule = forged.rfind(":rule ").expect("final proof step has a rule") + ":rule ".len();
    assert!(
        final_clause < rule,
        "the final rule proves the empty clause"
    );
    let end = forged[rule..]
        .find(|ch: char| ch.is_ascii_whitespace() || ch == ')')
        .map_or(forged.len(), |offset| rule + offset);
    assert_ne!(&forged[rule..end], "refl");
    // Refl can prove only an equality reflexivity literal, never an empty
    // clause. Keep the exact original conclusion/premises and forge its rule.
    forged.replace_range(rule..end, "refl");
    ay_core::pinned_carcara::pinned_carcara_can_judge(problem, &forged).unwrap();
    std::fs::write(&proof_path, &forged).unwrap();
    let (forged_status, output) = checker_run(
        &binary,
        &[
            std::ffi::OsStr::new("check"),
            std::ffi::OsStr::new("--"),
            proof_path.as_os_str(),
            problem_path.as_os_str(),
        ],
        directory.path(),
        "forged-empty-reflexivity",
    );
    assert!(
        output.lines().any(|line| line == "invalid"),
        "{output}\n{forged}"
    );
    if clean_dialect {
        // The transport discloses Clean-only dt_project. Both the original
        // and the forged final step must reach that reader on the same input.
        for (tag, document, valid) in [
            ("original", proof, true),
            ("forged", forged.as_str(), false),
        ] {
            let certificate = directory.path().join(format!("{tag}.json"));
            let payload = serde_json::json!({"type":"alethe_certificate", "version":"1.0", "problem": problem, "proof": document});
            std::fs::write(&certificate, serde_json::to_vec(&payload).unwrap()).unwrap();
            let (status, result) = checker_run(
                Path::new("clean"),
                &[
                    "cert".as_ref(),
                    "verify-external".as_ref(),
                    certificate.as_os_str(),
                ],
                directory.path(),
                tag,
            );
            assert_eq!(status.success(), valid, "{result}");
            if valid {
                assert!(result.contains("PASSED"), "{result}");
            }
        }
    }
    assert_eq!(before, Sha256::digest(std::fs::read(&binary).unwrap()));
    eprintln!("native datatype batch whole Carcara {} binary_sha256={:x} problem_sha256={:x} proof_sha256={:x}; forged empty-clause refl INVALID exit={forged_status}", version.trim(), before, Sha256::digest(problem.as_bytes()), Sha256::digest(proof.as_bytes()));
}

#[test]
fn native_datatype_batch_mutual_forward_constructor_selector_model_and_roundtrip() {
    let mut solver = Solver::new(Logic::All);
    let types = group();
    solver.push();
    let mut owner = budget(64 * 1024 * 1024, 64 * 1024 * 1024);
    let declared = solver.try_declare_datatypes_with_progress(&types, &mut owner, &mut |_, _| true);
    eprintln!(
        "fresh mutual datatype group at exact convenience envelope: result={declared:?} fees={:?}",
        owner.usage()
    );
    declared.unwrap();
    let nil = solver.datatype_constructor(&types[1], "batch_nil", &[]);
    let one = solver.int_const(1);
    let leaf = solver.datatype_constructor(&types[0], "batch_leaf", &[one]);
    let cons = solver.datatype_constructor(&types[1], "batch_cons", &[leaf, nil]);
    let node = solver.datatype_constructor(&types[0], "batch_node", &[cons]);
    let value = solver.declare_const("batch_tree_value", Sort::Datatype(types[0].clone()));
    let equality = solver.eq(value, node);
    solver.assert_term(equality);
    let children =
        solver.datatype_selector("batch_children", value, Sort::Datatype(types[1].clone()));
    let head = solver.datatype_selector("batch_head", children, Sort::Datatype(types[0].clone()));
    let payload = solver.datatype_selector("batch_value", head, Sort::Int);
    let same = solver.eq(payload, one);
    solver.assert_term(same);
    let is_node = solver.datatype_tester("batch_node", value);
    solver.assert_term(is_node);
    let details = solver.check_sat_with_details();
    assert!(details.result.is_sat(), "{details:?}");
    assert!(details.result.was_model_validated(), "{details:?}");
    assert!(solver.model().is_some());
    let artifact =
        solver.export_native_replay_artifact(NativeReplayMetadata::default(), Some(&details));
    assert_eq!(
        artifact
            .events
            .iter()
            .flat_map(|event| event.kind.datatypes())
            .cloned()
            .collect::<Vec<_>>(),
        types
    );
    assert!(
        matches!(&artifact.events[2].kind, NativeReplayEventKind::DeclareDatatypes { datatypes } if datatypes == &types)
    );
    let replay = Solver::replay_native_replay_json_str(&artifact.to_pretty_json()).unwrap();
    assert!(
        replay.result.is_sat() && replay.result.was_model_validated(),
        "{replay:?}"
    );
    let mut capture = NativeReplayExportBudget::new(NativeReplayExportLimits::new(
        32 * 1024 * 1024,
        16 * 1024 * 1024,
        4 * 1024 * 1024,
        128,
    ));
    let json = solver
        .try_export_native_replay_input_json(
            &NativeReplayMetadata::default(),
            &mut capture,
            &mut |_, _| true,
        )
        .unwrap();
    let replay = Solver::replay_native_replay_json_str(&json).unwrap();
    assert!(replay.result.is_sat() && replay.result.was_model_validated());
    solver.pop();
    // Native declarations remain global, including a group issued in a scope.
    let value = solver.datatype_constructor(&types[0], "batch_leaf", &[one]);
    assert_eq!(
        solver.get_sort(value),
        Sort::Datatype(types[0].clone()).as_term_sort()
    );
}

#[test]
fn native_datatype_batch_replay_rejects_forged_member_owner_and_sequential_split() {
    let mut solver = Solver::new(Logic::All);
    let types = group();
    solver.try_declare_datatypes(&types).unwrap();
    let nil = solver.datatype_constructor(&types[1], "batch_nil", &[]);
    let is_nil = solver.datatype_tester("batch_nil", nil);
    solver.assert_term(is_nil);
    let original = solver.export_native_replay_artifact(NativeReplayMetadata::default(), None);
    let mut forged = original.clone();
    let identity = forged
        .symbol_identities
        .iter_mut()
        .find(|identity| {
            identity.surface_name == "batch_nil"
                && identity.kind == NativeReplaySymbolKind::DatatypeConstructor
        })
        .unwrap();
    identity.datatype_surface = Some("BatchTree".into());
    assert!(Solver::replay_native_replay_artifact(&forged).is_err());
    let mut split = original;
    let index = split
        .events
        .iter()
        .position(|event| matches!(event.kind, NativeReplayEventKind::DeclareDatatypes { .. }))
        .unwrap();
    let depth = split.events[index].scope_depth;
    split.events[index].kind = NativeReplayEventKind::DeclareDatatype {
        datatype: types[0].clone(),
    };
    split.events.insert(
        index + 1,
        NativeReplayEvent::new(
            index + 1,
            NativeReplayEventKind::DeclareDatatype {
                datatype: types[1].clone(),
            },
            depth,
        ),
    );
    for (index, event) in split.events.iter_mut().enumerate() {
        event.index = index;
    }
    assert_eq!(
        split
            .events
            .iter()
            .flat_map(|event| event.kind.datatypes())
            .cloned()
            .collect::<Vec<_>>(),
        types,
        "the negative keeps both original declarations and their exact member metadata"
    );
    // Both definitions remain, but the first singleton would implicitly mint
    // the forward Forest carrier before its real declaration. Replaying that
    // history must refuse the collision rather than split one atomic group.
    assert!(Solver::replay_native_replay_artifact(&split).is_err());
}

#[test]
fn native_datatype_batch_distinct_constructors_require_a_transportable_strict_proof() {
    let mut solver = Solver::new(Logic::All);
    let types = group();
    solver.try_declare_datatypes(&types).unwrap();
    let zero = solver.int_const(0);
    let leaf = solver.datatype_constructor(&types[0], "batch_leaf", &[zero]);
    let nil = solver.datatype_constructor(&types[1], "batch_nil", &[]);
    let node = solver.datatype_constructor(&types[0], "batch_node", &[nil]);
    let value = solver.declare_const("batch_distinct_tree", Sort::Datatype(types[0].clone()));
    let equal_leaf = solver.eq(value, leaf);
    let equal_node = solver.eq(value, node);
    solver.assert_term(equal_leaf);
    solver.assert_term(equal_node);
    let artifact = solver.export_native_replay_artifact(NativeReplayMetadata::default(), None);
    let (details, proof) =
        Solver::replay_native_replay_artifact_with_checked_proof(&artifact, Duration::from_secs(5))
            .unwrap();
    if details.result.is_unknown() {
        // The typed checker knows disjoint constructors. Neither external
        // Alethe reader has a constructor-clash rule. Retain this exact case
        // as a wire-gap control until it has a portable derivation.
        let stats = &details.statistics;
        assert!(stats.proof_complete);
        assert_eq!(stats.get_int("proof_checker_total_steps"), Some(4));
        assert_eq!(stats.get_int("proof_checker_checked_steps"), Some(4));
        assert_eq!(stats.get_int("proof_checker_failures"), Some(0));
        assert_eq!(stats.get_int("proof_checker_skipped_hole_steps"), Some(0));
        assert_eq!(stats.get_int("proof_trust"), Some(0));
        assert!(!details.verification.unsat_proof_strictly_verified);
        assert_eq!(details.unknown_reason, Some(UnknownReason::ProofTrusted));
        assert!(
            details
                .unknown_diagnostic
                .as_ref()
                .and_then(|d| d.detail.as_deref())
                .is_some_and(|detail| detail.contains("known wire gap")),
            "{details:?}"
        );
        assert!(proof.is_none());
        return;
    }
    assert!(details.result.is_unsat(), "{details:?}");
    let proof = proof.expect("actual checked proof");
    proof
        .accept_for_consumer(ProofAcceptanceMode::Strict)
        .unwrap();
    assert_eq!(proof.quality.trust_count, 0);
    assert_eq!(proof.quality.hole_count, 0);
    let problem = proof
        .alethe_problem_smt2
        .as_ref()
        .expect("mutual declarations require a faithful paired problem");
    ay_core::pinned_carcara::pinned_carcara_can_judge(problem, &proof.alethe).unwrap();
    assert!(!proof.alethe.contains(":rule hole"));
    assert!(problem.contains("declare-datatypes"));
    check_whole_paired_document(problem, &proof.alethe, &proof.carcara_surface);
}

#[test]
fn native_datatype_batch_late_invalid_member_missing_sort_and_duplicates_are_atomic() {
    let mut solver = Solver::new(Logic::All);
    let before = solver.native_replay_events().len();
    let mut invalid = group();
    invalid[1].constructors[1].name = "and".into();
    assert!(solver.try_declare_datatypes(&invalid).is_err());
    assert!(solver
        .executor
        .context()
        .sort_definition("BatchTree")
        .is_none());
    assert!(solver
        .executor
        .context()
        .sort_definition("BatchForest")
        .is_none());
    assert_eq!(solver.native_replay_events().len(), before);
    for name in ["", "and", "__ay_private_member"] {
        for selector in [false, true] {
            let mut invalid = group();
            if selector {
                invalid[1].constructors[1].fields[0].name = name.into();
            } else {
                invalid[1].constructors[1].name = name.into();
            }
            assert!(
                solver.try_declare_datatypes(&invalid).is_err(),
                "{name:?}, selector={selector}"
            );
            assert_eq!(solver.native_replay_events().len(), before);
            assert!(solver
                .executor
                .context()
                .sort_definition("BatchTree")
                .is_none());
            assert!(solver
                .executor
                .context()
                .sort_definition("BatchForest")
                .is_none());
        }
    }
    invalid = group();
    invalid[1].constructors[1].fields[0].sort = Sort::Uninterpreted("MissingBatchType".into());
    assert!(solver.try_declare_datatypes(&invalid).is_err());
    assert!(solver
        .executor
        .context()
        .sort_definition("MissingBatchType")
        .is_none());
    let mut duplicate = group();
    duplicate[1].name = duplicate[0].name.clone();
    assert!(solver.try_declare_datatypes(&duplicate).is_err());
    let mut duplicate = group();
    duplicate[0].constructors[1].name = duplicate[0].constructors[0].name.clone();
    assert!(solver.try_declare_datatypes(&duplicate).is_err());
    assert_eq!(solver.native_replay_events().len(), before);
    solver.try_declare_datatypes(&group()).unwrap();
}

#[test]
fn native_datatype_batch_limits_and_late_cancel_keep_result_source_and_events() {
    let mut solver = Solver::new(Logic::All);
    let truth = solver.bool_const(true);
    solver.assert_term(truth);
    assert!(solver.check_sat_with_details().result.is_sat());
    let events = solver.native_replay_events().len();
    let terms = solver.terms().len();
    let mut owner = budget(0, 1024 * 1024);
    assert!(solver
        .try_declare_datatypes_with_progress(&group(), &mut owner, &mut |_, _| true)
        .is_err());
    assert!(matches!(
        owner.refusal(),
        Some(NativeDatatypeBatchRefusal::Work { .. })
    ));
    let mut owner = budget(usize::MAX / 4, usize::MAX / 4);
    let mut empty_polls = 0;
    assert!(solver
        .try_declare_datatypes_with_progress(&group(), &mut owner, &mut |work, storage| {
            if work == 0 && storage == 0 {
                empty_polls += 1;
            }
            empty_polls < 3
        })
        .is_err());
    assert_eq!(
        empty_polls, 3,
        "cancel at the final pre-commit poll after materialization"
    );
    assert!(owner.refusal().is_some());
    assert_eq!(solver.native_replay_events().len(), events);
    assert_eq!(solver.terms().len(), terms);
    assert!(solver
        .executor
        .context()
        .sort_definition("BatchTree")
        .is_none());
    assert!(
        solver.model().is_some(),
        "failed admission must preserve accepted prior model"
    );
    assert!(solver
        .try_declare_datatypes_with_progress(&group(), &mut owner, &mut |_, _| true)
        .is_err());
}

#[test]
fn native_datatype_batch_refuses_schematic_refresh_before_any_mutation() {
    let mut solver = Solver::new(Logic::All);
    solver
        .parse_smtlib2("(declare-sort-parameter T) (declare-fun id (T) T)")
        .unwrap();
    let before = solver.native_replay_events().len();
    assert!(solver.try_declare_datatypes(&group()).is_err());
    assert!(solver
        .executor
        .context()
        .sort_definition("BatchTree")
        .is_none());
    assert_eq!(solver.native_replay_events().len(), before);
}

#[test]
fn native_datatype_batch_resource_admission_precedes_deep_or_hidden_source_copy() {
    let mut solver = Solver::new(Logic::All);
    let mut types = group();
    let mut nested = Sort::Int;
    for _ in 0..32 {
        nested = Sort::array(Sort::Int, nested);
    }
    types[0].constructors[0].fields[0].sort = nested;
    let mut owner = NativeDatatypeBatchBudget::new(NativeDatatypeBatchLimits::new(
        usize::MAX / 4,
        usize::MAX / 4,
        4,
    ));
    assert!(solver
        .try_declare_datatypes_with_progress(&types, &mut owner, &mut |_, _| true)
        .is_err());
    assert!(matches!(
        owner.refusal(),
        Some(NativeDatatypeBatchRefusal::Depth { .. })
    ));
    assert!(solver
        .executor
        .context()
        .sort_definition("BatchTree")
        .is_none());
    let huge = format!("hidden_batch_sort_{}", "x".repeat(262_144));
    let _ = solver.declare_const("hidden_batch_value", Sort::Uninterpreted(huge));
    let mut owner = budget(10_000_000, 64 * 1024 * 1024);
    let before = solver.native_replay_events().len();
    assert!(solver
        .try_declare_datatypes_with_progress(&group(), &mut owner, &mut |_, _| true)
        .is_err());
    assert!(owner.refusal().is_some());
    assert_eq!(solver.native_replay_events().len(), before);
    assert!(solver
        .executor
        .context()
        .sort_definition("BatchTree")
        .is_none());
}

/// Keep a genuinely deep old signature in the live overload table AND two
/// lazy pre-scope snapshots. The new native constructor overloads that name,
/// so global snapshot propagation really exercises affected-primary clones.
fn old_signature_metadata() -> (Solver, FuncDecl, Vec<Sort>) {
    let mut solver = Solver::new(Logic::All);
    let domain = vec![Sort::array(Sort::Int, Sort::Bool); 32];
    let old = solver
        .try_declare_fun("batch_old_signature", &domain, Sort::Bool)
        .unwrap();
    solver.try_push().unwrap();
    solver
        .parse_smtlib2("(declare-fun batch_old_signature (Bool) Bool)")
        .unwrap();
    solver.try_push().unwrap();
    solver
        .parse_smtlib2("(declare-fun batch_old_signature (Int) Int)")
        .unwrap();
    (solver, old, domain)
}

fn old_signature_group() -> Vec<DatatypeSort> {
    vec![DatatypeSort::new(
        "BatchSignatureRecord",
        vec![DatatypeConstructor::new(
            "batch_old_signature",
            vec![DatatypeField::new("batch_signature_payload", Sort::Bool)],
        )],
    )]
}

#[test]
fn native_datatype_batch_old_signature_storage_prices_deep_clones_not_hash_slots() {
    let (mut solver, old, domain) = old_signature_metadata();
    let types = old_signature_group();
    let mut owner = budget(64 * 1024 * 1024, 64 * 1024 * 1024);
    let declared = solver.try_declare_datatypes_with_progress(&types, &mut owner, &mut |_, _| true);
    eprintln!("old live/overloaded/scoped signature at unchanged64Mi envelope: result={declared:?} fees={:?}", owner.usage());
    declared.unwrap();
    assert!(owner.usage().work > 0 && owner.usage().work <= 64 * 1024 * 1024);
    assert!(owner.usage().storage_bytes > 0 && owner.usage().storage_bytes <= 64 * 1024 * 1024);

    let truth = solver.bool_const(true);
    let record = solver
        .try_datatype_constructor(&types[0], "batch_old_signature", &[truth])
        .unwrap();
    let read = solver.datatype_selector("batch_signature_payload", record, Sort::Bool);
    assert_eq!(
        read, truth,
        "the new constructor keeps its own exact selector semantics"
    );
    solver.try_pop().unwrap();
    solver.try_pop().unwrap();
    let record = solver
        .try_datatype_constructor(&types[0], "batch_old_signature", &[truth])
        .unwrap();
    assert_eq!(
        solver.datatype_selector("batch_signature_payload", record, Sort::Bool),
        truth
    );
    assert!(
        solver.executor.context().has_symbol_with_signature(
            "batch_old_signature",
            &domain,
            &Sort::Bool
        ),
        "global member propagation must preserve the old native overload after both pops"
    );
    let array = solver.try_const_array(Sort::Int, truth).unwrap();
    assert!(
        solver.try_apply(&old, &vec![array; domain.len()]).is_ok(),
        "the old function handle must retain its original declaration identity"
    );
}

#[test]
fn native_datatype_batch_old_signature_tiny_and_cancelled_owners_stay_refused() {
    for cancel in [false, true] {
        let (mut solver, _, _) = old_signature_metadata();
        let types = old_signature_group();
        let events = solver.native_replay_events().len();
        let terms = solver.terms().len();
        let mut owner = budget(
            64 * 1024 * 1024,
            if cancel { 64 * 1024 * 1024 } else { 1024 },
        );
        assert!(solver
            .try_declare_datatypes_with_progress(&types, &mut owner, &mut |_, _| !cancel)
            .is_err());
        assert!(if cancel {
            matches!(owner.refusal(), Some(NativeDatatypeBatchRefusal::Cancelled))
        } else {
            matches!(
                owner.refusal(),
                Some(NativeDatatypeBatchRefusal::Storage { .. })
            )
        });
        assert!(solver
            .try_declare_datatypes_with_progress(&types, &mut owner, &mut |_, _| true)
            .is_err());
        assert_eq!(solver.native_replay_events().len(), events);
        assert_eq!(solver.terms().len(), terms);
        assert!(solver
            .executor
            .context()
            .sort_definition("BatchSignatureRecord")
            .is_none());
        // Only the original owner's refusal is sticky. No partial source
        // declaration can obstruct a fresh correctly sized owner.
        let mut fresh = budget(64 * 1024 * 1024, 64 * 1024 * 1024);
        solver
            .try_declare_datatypes_with_progress(&types, &mut fresh, &mut |_, _| true)
            .unwrap();
    }
}
