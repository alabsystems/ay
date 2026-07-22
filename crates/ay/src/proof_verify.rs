// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Post-solve proof verification (`--verify-proof`).
//!
//! When `--verify-proof` is enabled (or under `cfg(debug_assertions)` by
//! default), eligible DIMACS UNSAT results are re-checked by invoking the
//! internal `ay_drat_check` / `ay_lrat_check` checker on the emitted proof. A
//! rejected proof is a soundness failure: the result is downgraded to an error
//! and the process exits non-zero (#8771).
//!
//! This module owns the file-IO / format-dispatch glue between the main
//! DIMACS solve path and the checker crates. Alethe and Lean4 formats are
//! not supported by the internal checker; for those formats
//! `--verify-proof` is silently a no-op and a `c Warning:` is emitted so the
//! user is not misled into believing the proof was checked.

use std::fs;
use std::path::Path;

use super::{ProofConfig, ProofFormat};

/// Outcome of a post-solve proof verification pass.
#[derive(Debug)]
pub(crate) enum VerifyOutcome {
    /// The internal checker accepted the proof.
    Verified,
    /// The internal checker rejected the proof. This is a soundness failure;
    /// the caller MUST NOT treat the solve result as trustworthy.
    Rejected { reason: String },
    /// The verifier did not run (unsupported format, I/O error, etc.).
    /// Carries a human-readable explanation for the warning log.
    Skipped { reason: String },
}

/// Verify the emitted proof file against the original DIMACS content.
///
/// * `dimacs_content` is the raw CNF source (same bytes that were fed into the
///   solver). Re-parsing here ensures the checker sees the exact original
///   clauses, not any inprocessed/simplified version.
/// * `proof_config.path` is the proof file that the solver just finished
///   writing. The caller MUST flush/close the proof writer before invoking
///   this function.
pub(crate) fn verify_proof_file(dimacs_content: &str, proof_config: &ProofConfig) -> VerifyOutcome {
    let proof_path = Path::new(&proof_config.path);
    let proof_bytes = match fs::read(proof_path) {
        Ok(bytes) => bytes,
        Err(err) => {
            return VerifyOutcome::Skipped {
                reason: format!("failed to read proof file {}: {err}", proof_config.path),
            }
        }
    };
    if proof_bytes.is_empty() {
        return VerifyOutcome::Rejected {
            reason: format!(
                "proof file {} is empty (0 bytes) — solver produced no proof",
                proof_config.path
            ),
        };
    }

    match proof_config.format {
        ProofFormat::Drat => verify_drat(dimacs_content, &proof_bytes),
        ProofFormat::Lrat => verify_lrat(dimacs_content, &proof_bytes),
        ProofFormat::Alethe => VerifyOutcome::Skipped {
            reason: "Alethe proof format not supported by internal checker \
                     (use --proof-format drat or lrat to enable --verify-proof)"
                .to_string(),
        },
        ProofFormat::Lean4 => VerifyOutcome::Skipped {
            reason: "Lean4 proof format not supported by internal checker \
                     (use --proof-format drat or lrat to enable --verify-proof)"
                .to_string(),
        },
    }
}

fn verify_drat(dimacs_content: &str, proof_bytes: &[u8]) -> VerifyOutcome {
    use ay_drat_check::checker::DratChecker;
    use ay_drat_check::cnf_parser::parse_cnf;
    use ay_drat_check::drat_parser::{parse_drat, ProofStep};
    use ay_drat_check::SrChecker;

    let cnf = match parse_cnf(dimacs_content.as_bytes()) {
        Ok(c) => c,
        Err(err) => {
            return VerifyOutcome::Skipped {
                reason: format!("re-parse of DIMACS for checker failed: {err}"),
            }
        }
    };
    if cnf.num_vars > ay_drat_check::checker::MAX_DENSE_VARS {
        return VerifyOutcome::Rejected {
            reason: format!(
                "formula variable count {} exceeds DRAT checker's dense maximum {}",
                cnf.num_vars,
                ay_drat_check::checker::MAX_DENSE_VARS
            ),
        };
    }
    let steps = match parse_drat(proof_bytes) {
        Ok(s) => s,
        Err(err) => {
            return VerifyOutcome::Rejected {
                reason: format!("DRAT proof parse error: {err}"),
            }
        }
    };
    if steps.is_empty() {
        return VerifyOutcome::Rejected {
            reason: "DRAT proof contains zero steps".to_string(),
        };
    }

    // PR/SR (DPR/DSR) proofs carry a witness section on `a`-lines, parsed as
    // `AddPr`. The plain RUP/RAT DRAT checker fails closed on those; route the
    // whole proof through the NATIVE PR/SR checker instead (it still handles the
    // RUP/RAT `Add` steps, and decides each witnessed step by reverse unit
    // propagation). This is the in-product self-check for the SR emit route.
    let has_witness = steps
        .iter()
        .any(|step| matches!(step, ProofStep::AddPr { .. }));
    if has_witness {
        let mut checker = SrChecker::new(cnf.num_vars, true);
        return match checker.verify(&cnf.clauses, &steps) {
            Ok(()) => VerifyOutcome::Verified,
            Err(err) => VerifyOutcome::Rejected {
                reason: format!("PR/SR checker rejected proof: {err}"),
            },
        };
    }

    let mut checker = DratChecker::new(cnf.num_vars, true);
    match checker.verify(&cnf.clauses, &steps) {
        Ok(()) => VerifyOutcome::Verified,
        Err(err) => VerifyOutcome::Rejected {
            reason: format!("DRAT checker rejected proof: {err}"),
        },
    }
}

fn verify_lrat(dimacs_content: &str, proof_bytes: &[u8]) -> VerifyOutcome {
    use ay_lrat_check::checker::LratChecker;
    use ay_lrat_check::dimacs::parse_cnf_with_ids;
    use ay_lrat_check::lrat_parser::{is_binary_lrat, parse_binary_lrat, parse_text_lrat};

    let cnf = match parse_cnf_with_ids(dimacs_content.as_bytes()) {
        Ok(c) => c,
        Err(err) => {
            return VerifyOutcome::Skipped {
                reason: format!("re-parse of DIMACS for checker failed: {err}"),
            }
        }
    };
    if cnf.num_vars > ay_lrat_check::checker::MAX_DENSE_VARS {
        return VerifyOutcome::Rejected {
            reason: format!(
                "formula variable count {} exceeds LRAT checker's dense maximum {}",
                cnf.num_vars,
                ay_lrat_check::checker::MAX_DENSE_VARS
            ),
        };
    }
    let steps_result = if is_binary_lrat(proof_bytes) {
        parse_binary_lrat(proof_bytes).map_err(|e| e.to_string())
    } else {
        match std::str::from_utf8(proof_bytes) {
            Ok(s) => parse_text_lrat(s).map_err(|e| e.to_string()),
            Err(e) => Err(format!("LRAT proof is not valid UTF-8: {e}")),
        }
    };
    let steps = match steps_result {
        Ok(s) => s,
        Err(err) => {
            return VerifyOutcome::Rejected {
                reason: format!("LRAT proof parse error: {err}"),
            }
        }
    };
    if steps.is_empty() {
        return VerifyOutcome::Rejected {
            reason: "LRAT proof contains zero steps".to_string(),
        };
    }
    let mut checker = LratChecker::new(cnf.num_vars);
    for (id, clause) in &cnf.clauses {
        checker.add_original(*id, clause);
    }
    if checker.verify_proof(&steps) {
        VerifyOutcome::Verified
    } else {
        VerifyOutcome::Rejected {
            reason: format!(
                "LRAT checker rejected proof ({} failures)",
                checker.stats().failures
            ),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // A trivially UNSAT formula and a minimal valid DRAT proof.
    // Clauses: (1) (-1). Empty clause is derivable.
    const TRIVIAL_UNSAT_CNF: &str = "p cnf 1 2\n1 0\n-1 0\n";

    #[test]
    fn test_verify_drat_accepts_valid_proof() {
        // Valid DRAT: derive the empty clause.
        let proof = b"0\n";
        let config = ProofConfig::new(write_temp_proof(proof, "drat"), ProofFormat::Drat, false);
        let outcome = verify_proof_file(TRIVIAL_UNSAT_CNF, &config);
        assert!(
            matches!(outcome, VerifyOutcome::Verified),
            "expected Verified, got: {outcome:?}"
        );
        let _ = fs::remove_file(&config.path);
    }

    #[test]
    fn test_verify_drat_rejects_proof_for_sat_formula() {
        // A satisfiable formula (just "1") cannot be proven UNSAT. Any DRAT
        // proof claiming to derive the empty clause MUST be rejected.
        let sat_cnf = "p cnf 1 1\n1 0\n";
        let proof = b"0\n";
        let config = ProofConfig::new(write_temp_proof(proof, "drat"), ProofFormat::Drat, false);
        let outcome = verify_proof_file(sat_cnf, &config);
        assert!(
            matches!(outcome, VerifyOutcome::Rejected { .. }),
            "expected Rejected for SAT-formula proof, got: {outcome:?}"
        );
        let _ = fs::remove_file(&config.path);
    }

    #[test]
    fn test_verify_drat_rejects_empty_proof() {
        let config = ProofConfig::new(write_temp_proof(b"", "drat"), ProofFormat::Drat, false);
        let outcome = verify_proof_file(TRIVIAL_UNSAT_CNF, &config);
        assert!(
            matches!(outcome, VerifyOutcome::Rejected { .. }),
            "expected Rejected for empty proof, got: {outcome:?}"
        );
        let _ = fs::remove_file(&config.path);
    }

    #[test]
    fn test_verify_skips_alethe_format() {
        let config = ProofConfig::new(
            write_temp_proof(b"(anything)\n", "alethe"),
            ProofFormat::Alethe,
            false,
        );
        let outcome = verify_proof_file(TRIVIAL_UNSAT_CNF, &config);
        assert!(
            matches!(outcome, VerifyOutcome::Skipped { .. }),
            "expected Skipped for Alethe, got: {outcome:?}"
        );
        let _ = fs::remove_file(&config.path);
    }

    fn write_temp_proof(bytes: &[u8], ext: &str) -> String {
        use std::io::Write;
        let mut path = std::env::temp_dir();
        let nanos = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_nanos())
            .unwrap_or(0);
        path.push(format!("ay-verify-test-{nanos}.{ext}"));
        let mut file = fs::File::create(&path).expect("create temp proof");
        file.write_all(bytes).expect("write temp proof");
        file.flush().expect("flush temp proof");
        path.to_string_lossy().into_owned()
    }
}
