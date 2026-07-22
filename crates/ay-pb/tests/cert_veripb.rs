// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// End-to-end DEC-LIN-CERT validation: AY produces a VeriPB v3 proof of a PB
// instance's UNSATISFIABILITY via the SAT-encoding path (DRAT lifted to VeriPB),
// and the OFFICIAL VeriPB checker accepts it. Gated on the checker being present
// (VERIPB_BIN env or `veripb` on PATH) so CI without it skips.

use std::io::Write;
use std::path::PathBuf;
use std::process::Command;

fn veripb_bin() -> Option<PathBuf> {
    if let Some(p) = std::env::var_os("VERIPB_BIN") {
        let p = PathBuf::from(p);
        if p.exists() {
            return Some(p);
        }
    }
    // Fall back to `veripb` resolved from PATH.
    std::env::var_os("PATH").and_then(|paths| {
        std::env::split_paths(&paths)
            .map(|dir| dir.join("veripb"))
            .find(|p| p.is_file())
    })
}

fn repo_instance(rel: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(rel)
}

/// Certify `rel` (an UNSAT OPB) and confirm the OFFICIAL VeriPB checker verifies.
fn assert_certified_unsat(rel: &str) {
    let Some(veripb) = veripb_bin() else {
        eprintln!("VeriPB checker not present; skipping {rel}");
        return;
    };
    let opb_path = repo_instance(rel);
    let input = std::fs::read_to_string(&opb_path).expect("read opb");
    let instance = ay_pb::parse_opb(&input).expect("parse opb");

    let pbp = ay_pb::proof::certify_decision_unsat(&instance)
        .unwrap_or_else(|| panic!("expected a certified-UNSAT proof for {rel}"));

    let stem = rel.rsplit('/').next().unwrap_or("inst").replace('.', "_");
    let proof_path = std::env::temp_dir().join(format!("ay_cert_{stem}.pbp"));
    {
        let mut f = std::fs::File::create(&proof_path).expect("create proof file");
        f.write_all(pbp.as_bytes()).expect("write proof");
    }

    let output = Command::new(&veripb)
        .arg(&opb_path)
        .arg(&proof_path)
        .output()
        .expect("run veripb");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stdout.contains("VERIFIED UNSATISFIABLE"),
        "VeriPB did not verify {rel}\nstdout: {stdout}\nstderr: {stderr}\nproof:\n{pbp}"
    );
}

#[test]
fn trivial_unsat_is_veripb_certified() {
    assert_certified_unsat("../../benchmarks/pb-comp/test-instances/trivial-unsat.opb");
}

#[test]
fn clausal_unsat_is_veripb_certified() {
    // Pure-clausal multi-clause refutation: the clause fast-path keeps it aux-free
    // so the multi-line DRAT lifts 1:1 to VeriPB rup steps (increment 1.5).
    assert_certified_unsat("../../benchmarks/pb-comp/test-instances/clausal-unsat-2x4.opb");
}

#[test]
#[ignore = "coverage probe over the koops DEC-LIN family; run with --ignored --nocapture"]
fn koops_cert_coverage_probe() {
    let Some(veripb) = veripb_bin() else {
        eprintln!("VeriPB checker not present; skipping coverage probe");
        return;
    };
    let dir = repo_instance("../../benchmarks/pb-comp/normalized-PB25/DEC-LIN/koops");
    let mut entries: Vec<_> = std::fs::read_dir(&dir)
        .expect("koops dir")
        .filter_map(|e| e.ok())
        .map(|e| e.path())
        .filter(|p| p.extension().is_some_and(|x| x == "opb"))
        .collect();
    entries.sort();
    let (mut certified, mut declined, mut total) = (0, 0, 0);
    for p in &entries {
        total += 1;
        let name = p.file_name().unwrap().to_string_lossy().to_string();
        let input = std::fs::read_to_string(p).expect("read");
        let Ok(instance) = ay_pb::parse_opb(&input) else {
            eprintln!("  {name}: PARSE-FAIL");
            continue;
        };
        match ay_pb::proof::certify_decision_unsat(&instance) {
            Some(pbp) => {
                let proof_path = std::env::temp_dir().join(format!("ay_cov_{total}.pbp"));
                std::fs::write(&proof_path, &pbp).expect("write proof");
                let out = Command::new(&veripb)
                    .arg(p)
                    .arg(&proof_path)
                    .output()
                    .expect("veripb");
                let ok = String::from_utf8_lossy(&out.stdout).contains("VERIFIED UNSATISFIABLE");
                let _ = std::fs::remove_file(&proof_path);
                if ok {
                    certified += 1;
                    eprintln!("  {name}: CERTIFIED ({} B)", pbp.len());
                } else {
                    eprintln!("  {name}: PROOF-REJECTED");
                }
            }
            None => {
                declined += 1;
                eprintln!("  {name}: declined (aux/SAT/unknown)");
            }
        }
    }
    eprintln!("KOOPS CERT COVERAGE: {certified}/{total} certified, {declined} declined");
}

#[test]
#[ignore = "real competition instance (slow: full SAT solve + VeriPB check); run with --ignored"]
fn koops_mat98_identity_complement_is_veripb_certified() {
    // A real PB25 DEC-LIN koops instance. Its cardinality rows (at-least-1,
    // at-most-1, at-least-2) all decompose aux-free, so the strong SAT path's DRAT
    // lifts to a VeriPB proof the official checker accepts — a genuine DEC-LIN-CERT.
    assert_certified_unsat(
        "../../benchmarks/pb-comp/normalized-PB25/DEC-LIN/koops/normalized-mat98_identity_complement.opb",
    );
}

#[test]
fn pigeonhole_3_2_is_veripb_certified() {
    // At-most-1 (`x_a + x_b + x_c <= 1`) normalizes to at-least-2 (`>= n-1`), which
    // the pairwise fast-path emits as aux-free clauses — so the whole pigeonhole
    // refutation lifts to VeriPB. First certified *cardinality-class* instance.
    assert_certified_unsat("../../benchmarks/pb-comp/test-instances/pigeonhole-3-2.opb");
}
