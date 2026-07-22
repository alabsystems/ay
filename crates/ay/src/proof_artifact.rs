// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Lean 4 `proof-artifact-v1` sidecar writer for emitted ay proof files.

use std::collections::BTreeMap;
use std::fs;
use std::io;

use serde_json::{json, Value};
use sha2::{Digest, Sha256};

use crate::{stats_output, ProofConfig, ProofFormat};

const PROOF_ARTIFACT_VERSION: &str = "proof-artifact-v1";

#[derive(Clone, Copy, Debug)]
pub(crate) enum ProofArtifactProblem<'a> {
    Text(&'a str),
    FilePath(&'a str),
    Unavailable(&'static str),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ProofArtifactTheoryMetadata {
    solver_mode: String,
    logic: String,
    theories: Vec<String>,
    details: BTreeMap<String, String>,
}

impl ProofArtifactTheoryMetadata {
    pub(crate) fn dimacs_sat(num_vars: usize, num_original_clauses: usize) -> Self {
        let mut details = BTreeMap::new();
        details.insert("num_vars".to_string(), num_vars.to_string());
        details.insert(
            "num_original_clauses".to_string(),
            num_original_clauses.to_string(),
        );
        Self {
            solver_mode: "dimacs-sat".to_string(),
            logic: "DIMACS-CNF".to_string(),
            theories: vec!["sat".to_string()],
            details,
        }
    }

    pub(crate) fn smt_lib(
        logic: Option<&str>,
        formula_stats: Option<&ay_frontend::FormulaStats>,
    ) -> Self {
        let mut details = BTreeMap::new();
        let mut theories = Vec::new();

        if let Some(stats) = formula_stats {
            details.insert("commands".to_string(), stats.commands.to_string());
            details.insert("terms".to_string(), stats.terms.to_string());
            for (theory, count) in &stats.theory_usage {
                theories.push(theory.clone());
                details.insert(format!("theory.{theory}.uses"), count.to_string());
            }
            for (sort, count) in &stats.sort_distribution {
                details.insert(format!("sort.{sort}.uses"), count.to_string());
            }
        }

        if theories.is_empty() {
            theories.push("unknown".to_string());
        }

        Self {
            solver_mode: "smt-lib".to_string(),
            logic: logic.unwrap_or("SMT-LIB").to_string(),
            theories,
            details,
        }
    }

    fn json_value(&self) -> Value {
        json!({
            "solver_mode": self.solver_mode,
            "logic": self.logic,
            "theories": self.theories,
            "details": self.details,
        })
    }

    fn metadata_strings(&self) -> BTreeMap<String, String> {
        let mut metadata = BTreeMap::new();
        metadata.insert("solver_mode".to_string(), self.solver_mode.clone());
        metadata.insert("logic".to_string(), self.logic.clone());
        metadata.insert("theories".to_string(), self.theories.join(","));
        for (key, value) in &self.details {
            metadata.insert(format!("theory_metadata.{key}"), value.clone());
        }
        metadata
    }
}

pub(crate) fn write_proof_artifact_or_exit(
    problem: ProofArtifactProblem<'_>,
    proof_config: &ProofConfig,
    theory: ProofArtifactTheoryMetadata,
) {
    let Some(path) = proof_config.artifact_path.as_deref() else {
        return;
    };

    if let Err(error) = write_proof_artifact(path, problem, proof_config, theory) {
        safe_eprintln!("Error: failed to write proof artifact {path}: {error}");
        std::process::exit(1);
    }
}

fn write_proof_artifact(
    artifact_path: &str,
    problem: ProofArtifactProblem<'_>,
    proof_config: &ProofConfig,
    theory: ProofArtifactTheoryMetadata,
) -> io::Result<()> {
    let (problem_bytes, input_source) = read_problem_bytes(problem)?;
    let proof_bytes = fs::read(&proof_config.path)?;

    let input_hash = sha256_prefixed(&problem_bytes);
    let proof_hash = sha256_prefixed(&proof_bytes);
    let proof_format = proof_format_name(proof_config.format);
    let proof_encoding = if proof_config.binary {
        "binary"
    } else {
        "text"
    };
    let proof_payload = proof_payload_value(&proof_bytes, proof_config.binary);
    let problem_text = String::from_utf8_lossy(&problem_bytes).into_owned();

    let mut metadata = theory.metadata_strings();
    metadata.insert("input_hash".to_string(), input_hash.clone());
    metadata.insert("input_source".to_string(), input_source);
    metadata.insert("proof_format".to_string(), proof_format.to_string());
    metadata.insert("proof_encoding".to_string(), proof_encoding.to_string());
    metadata.insert("proof_path".to_string(), proof_config.path.clone());
    metadata.insert(
        "model_hash_role".to_string(),
        "same_as_problem_hash_for_ay_solver_input".to_string(),
    );

    let artifact = json!({
        "version": PROOF_ARTIFACT_VERSION,
        "producer": {
            "repo": env!("CARGO_PKG_REPOSITORY"),
            "commit": stats_output::BUILD_PROVENANCE.commit,
            "name": "ay",
            "version": stats_output::BUILD_PROVENANCE.version,
        },
        "source_system": "ay",
        "problem_hash": input_hash,
        "model_hash": input_hash,
        "proof_hash": proof_hash,
        "artifact_kind": "ay_proof_artifact",
        "verifier_constants": [],
        "certificate": {
            "format": format!("ay-{proof_format}-envelope-v1"),
            "encoding": "json",
            "payload_hash": proof_hash,
            "payload": {
                "type": "ay_proof_certificate",
                "version": "1.0",
                "problem": problem_text,
                "proof": proof_payload,
                "proof_format": proof_format,
                "proof_encoding": proof_encoding,
                "theory_metadata": theory.json_value(),
            }
        },
        "metadata": metadata,
    });

    let json = serde_json::to_string_pretty(&artifact)
        .map_err(|error| io::Error::new(io::ErrorKind::InvalidData, error))?;
    fs::write(artifact_path, format!("{json}\n"))
}

fn read_problem_bytes(problem: ProofArtifactProblem<'_>) -> io::Result<(Vec<u8>, String)> {
    match problem {
        ProofArtifactProblem::Text(text) => Ok((text.as_bytes().to_vec(), "inline".to_string())),
        ProofArtifactProblem::FilePath(path) => {
            fs::read(path).map(|bytes| (bytes, path.to_string()))
        }
        ProofArtifactProblem::Unavailable(reason) => Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            format!("input bytes unavailable for proof-artifact-v1 envelope: {reason}"),
        )),
    }
}

fn proof_payload_value(proof_bytes: &[u8], force_hex: bool) -> Value {
    if !force_hex {
        if let Ok(text) = std::str::from_utf8(proof_bytes) {
            return json!({
                "encoding": "text",
                "text": text,
            });
        }
    }

    json!({
        "encoding": "hex",
        "hex": hex_encode(proof_bytes),
    })
}

fn proof_format_name(format: ProofFormat) -> &'static str {
    match format {
        ProofFormat::Drat => "drat",
        ProofFormat::Lrat => "lrat",
        ProofFormat::Lean4 => "lean4",
        ProofFormat::Alethe => "alethe",
    }
}

fn sha256_prefixed(bytes: &[u8]) -> String {
    let digest = Sha256::digest(bytes);
    format!("sha256:{}", hex_encode(&digest))
}

fn hex_encode(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(bytes.len() * 2);
    for &byte in bytes {
        out.push(HEX[(byte >> 4) as usize] as char);
        out.push(HEX[(byte & 0x0f) as usize] as char);
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sha256_hashes_are_prefixed_lowercase_hex() {
        assert_eq!(
            sha256_prefixed(b"abc"),
            "sha256:ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        );
    }

    #[test]
    fn binary_payload_uses_hex() {
        let payload = proof_payload_value(&[0, 15, 255], true);
        assert_eq!(payload["encoding"], "hex");
        assert_eq!(payload["hex"], "000fff");
    }
}
