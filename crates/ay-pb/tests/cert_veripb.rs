// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// Fresh-checkout coverage in this file is deliberately GENERATED_UNVERIFIED:
// it proves that AY emits structurally complete VeriPB v3 text, but structure
// is not external certification. The `certified-proof-artifacts` feature adds
// a fail-closed gate that requires the official VeriPB checker.

use std::path::PathBuf;

const TRIVIAL_UNSAT: &str = "../../benchmarks/pb-comp/test-instances/trivial-unsat.opb";
const CLAUSAL_UNSAT: &str = "../../benchmarks/pb-comp/test-instances/clausal-unsat-2x4.opb";
const PIGEONHOLE_UNSAT: &str = "../../benchmarks/pb-comp/test-instances/pigeonhole-3-2.opb";

fn repo_instance(rel: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(rel)
}

fn assert_unsat_pbp_structure(rel: &str, instance: &ay_pb::PbInstance, pbp: &str) {
    assert!(!pbp.trim().is_empty(), "{rel}: proof must be nonempty");
    assert!(
        pbp.starts_with("pseudo-Boolean proof version 3.0\n"),
        "{rel}: missing VeriPB v3 header\n{pbp}"
    );
    let input_rows =
        ay_pb::veripb_input_constraint_count(instance).expect("input row count fits u64");
    let formula_declaration = format!("f {input_rows} ;");
    assert!(
        pbp.lines().any(|line| line == formula_declaration.as_str()),
        "{rel}: missing or wrong formula-count declaration\n{pbp}"
    );
    assert_eq!(
        pbp.lines().filter(|line| *line == "output NONE;").count(),
        1,
        "{rel}: proof must contain exactly one output declaration\n{pbp}"
    );
    let conclusion_ids: Vec<_> = pbp
        .lines()
        .filter_map(|line| {
            line.strip_prefix("conclusion UNSAT : ")
                .and_then(|id| id.strip_suffix(';'))
        })
        .collect();
    assert_eq!(
        conclusion_ids.len(),
        1,
        "{rel}: proof must contain exactly one indexed UNSAT conclusion\n{pbp}"
    );
    assert!(
        conclusion_ids[0].parse::<u64>().is_ok_and(|id| id > 0),
        "{rel}: UNSAT conclusion id is not positive\n{pbp}"
    );
    assert!(
        pbp.ends_with("end pseudo-Boolean proof;\n"),
        "{rel}: proof is not terminated\n{pbp}"
    );
}

struct GeneratedUnverified {
    opb_path: PathBuf,
    instance: ay_pb::PbInstance,
    proof: String,
}

/// Generate proof text and check its shape. This helper intentionally does not
/// certify or verify the proof; callers must keep the GENERATED_UNVERIFIED
/// label unless they additionally pass the proof through VeriPB.
fn generate_unverified(rel: &str) -> GeneratedUnverified {
    let opb_path = repo_instance(rel);
    let input = std::fs::read_to_string(&opb_path).expect("read opb");
    let instance = ay_pb::parse_opb(&input).expect("parse opb");
    let proof = ay_pb::proof::certify_decision_unsat(&instance)
        .unwrap_or_else(|| panic!("expected generated proof text for {rel}"));
    assert_unsat_pbp_structure(rel, &instance, &proof);
    GeneratedUnverified {
        opb_path,
        instance,
        proof,
    }
}

#[test]
fn trivial_unsat_proof_is_generated_unverified_shape_only() {
    let generated = generate_unverified(TRIVIAL_UNSAT);
    assert!(generated.opb_path.is_file());
    assert_eq!(generated.instance.num_vars, 1);
}

#[test]
fn clausal_unsat_proof_is_generated_unverified_shape_only() {
    // Pure-clausal multi-clause refutation: the clause fast-path keeps it
    // auxiliary-variable-free so its DRAT steps can be lifted.
    let generated = generate_unverified(CLAUSAL_UNSAT);
    assert!(!generated.proof.is_empty());
}

#[test]
fn pigeonhole_3_2_proof_is_generated_unverified_shape_only() {
    // This is cardinality-class generation coverage. It remains explicitly
    // unverified in a fresh checkout.
    let generated = generate_unverified(PIGEONHOLE_UNSAT);
    assert_eq!(generated.instance.num_vars, 6);
}

#[cfg(feature = "certified-proof-artifacts")]
mod certified_gate {
    use std::fs::OpenOptions;
    use std::io::Write;
    use std::path::{Path, PathBuf};

    use ay_pb::veripb_runner::{verify_unsat, VeriPbEnvelope};

    use super::{generate_unverified, CLAUSAL_UNSAT, PIGEONHOLE_UNSAT, TRIVIAL_UNSAT};

    struct TemporaryProof {
        path: PathBuf,
    }

    impl Drop for TemporaryProof {
        fn drop(&mut self) {
            let _ = std::fs::remove_file(&self.path);
        }
    }

    fn required_veripb() -> PathBuf {
        if let Some(raw) = std::env::var_os("VERIPB_BIN") {
            let path = PathBuf::from(raw);
            assert!(
                path.is_file(),
                "certified-proof-artifacts requires VERIPB_BIN to name a file; got {}",
                path.display()
            );
            return path;
        }
        if let Some(paths) = std::env::var_os("PATH") {
            let executable = format!("veripb{}", std::env::consts::EXE_SUFFIX);
            if let Some(path) = std::env::split_paths(&paths)
                .map(|directory| directory.join(&executable))
                .find(|path| path.is_file())
            {
                return path;
            }
        }
        panic!(
            "certified-proof-artifacts requires the official VeriPB checker; \
             set VERIPB_BIN or put veripb on PATH"
        );
    }

    fn temporary_proof(label: &str, proof: &str) -> TemporaryProof {
        for attempt in 0..100u32 {
            let path = std::env::temp_dir().join(format!(
                "ay-cert-veripb-{}-{label}-{attempt}.pbp",
                std::process::id()
            ));
            match OpenOptions::new().write(true).create_new(true).open(&path) {
                Ok(mut output) => {
                    output.write_all(proof.as_bytes()).expect("write proof");
                    return TemporaryProof { path };
                }
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => panic!("create {}: {error}", path.display()),
            }
        }
        panic!("could not reserve a temporary proof path for {label}");
    }

    fn assert_veripb_verified(checker: &Path, rel: &str, label: &str) {
        let generated = generate_unverified(rel);
        let proof_file = temporary_proof(label, &generated.proof);
        let envelope = VeriPbEnvelope::bounded_default();
        eprintln!(
            "VERIPB_ENVELOPE_V1 checker={} {}",
            checker.display(),
            envelope.record()
        );
        verify_unsat(checker, &generated.opb_path, &proof_file.path, envelope)
            .unwrap_or_else(|error| panic!("VeriPB did not verify {rel}: {error}"));
    }

    #[test]
    fn generated_proofs_are_veripb_verified_under_certification_gate() {
        let checker = required_veripb();
        assert_veripb_verified(&checker, TRIVIAL_UNSAT, "trivial");
        assert_veripb_verified(&checker, CLAUSAL_UNSAT, "clausal");
        assert_veripb_verified(&checker, PIGEONHOLE_UNSAT, "pigeonhole");
    }
}
