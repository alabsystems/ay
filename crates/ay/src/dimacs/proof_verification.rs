// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

/// Verify the emitted Lean4 proof file post-UNSAT when `--lean-verify` is
/// enabled (#8773, Phase 1 thin wrapper). Returns `true` when the proof is
/// accepted, `false` when an explicitly requested kernel check cannot run or
/// rejects the exact proof generation emitted by this solve.
///
/// Exit-code contract (see the development design notes):
/// - Accepted  → true  (caller proceeds to exit 20 = UNSAT)
/// - Rejected  → false (caller should exit 2 = soundness failure)
/// - Unavailable (lean missing, timeout, IO error) → false (the explicit
///   verification promise was not fulfilled).
///
/// Safe to call unconditionally; it becomes a no-op when `--lean-verify` is
/// disabled or the emitted proof is not Lean4.
#[must_use]
fn verify_lean_proof(proof_config: Option<&ProofConfig>) -> bool {
    verify_lean_proof_body(proof_config)
}

fn cleanup_temp_proof_file(proof: &ProofConfig) {
    if proof.is_temp {
        let _ = remove_owned_dimacs_proof(&proof.path);
    }
}

fn verification_skip_is_acceptable(explicitly_requested: bool) -> bool {
    !explicitly_requested && required_dimacs_proof_gate_name().is_none()
}

/// Verify the emitted proof file post-UNSAT when `--verify-proof` is enabled
/// (#8771). Returns `true` when the proof is accepted (or verification was
/// skipped because the flag is off / the format is unsupported), `false` when
/// the internal checker rejects the proof — a soundness failure.
///
/// Safe to call unconditionally; it becomes a no-op when verification is
/// disabled or no proof was emitted.
#[must_use]
fn verify_unsat_proof(content: &str, proof_config: Option<&ProofConfig>) -> bool {
    // Check the atomic directly so CHC / interactive paths that don't build
    // a proof config still see the flag state (they do not produce SAT proofs
    // so this is a pure short-circuit for them).
    if !super::VERIFY_PROOF_ENABLED.load(Ordering::SeqCst) {
        return true;
    }
    let explicitly_requested = super::EXPLICIT_VERIFY_PROOF_ENABLED.load(Ordering::SeqCst);
    let proof = match proof_config {
        Some(p) => p,
        None if explicitly_requested => {
            safe_eprintln!("c Error: --verify-proof set but no proof was emitted");
            return false;
        }
        None => return true,
    };
    let optional_default = synthesized_default_dimacs_proof_is_optional(proof);

    let expected_sha256 = match published_dimacs_proof(&proof.path) {
        Ok(published) => published.sha256,
        Err(error) => {
            if optional_default {
                safe_eprintln!(
                    "c Warning: automatic proof verification skipped output not emitted by this run: {error}"
                );
            } else {
                safe_eprintln!(
                    "c Error: proof verification refused output not emitted by this run: {error}"
                );
            }
            cleanup_temp_proof_file(proof);
            return false;
        }
    };

    use super::proof_verify::{verify_proof_file, VerifyOutcome};
    let outcome = verify_proof_file(content, proof, expected_sha256);

    match outcome {
        VerifyOutcome::Verified => {
            safe_eprintln!(
                "c verify-proof: {} verified ({} format)",
                proof.path,
                match proof.format {
                    ProofFormat::Drat => "DRAT",
                    ProofFormat::Lrat => "LRAT",
                    ProofFormat::Alethe => "Alethe",
                    ProofFormat::Lean4 => "Lean4",
                    ProofFormat::Veripb => "VeriPB",
                }
            );
            true
        }
        VerifyOutcome::Skipped { reason } => {
            let required_gate = required_dimacs_proof_gate_name();
            if let Some(gate) = required_gate {
                safe_eprintln!("c Error: {gate} DIMACS proof re-check could not run: {reason}");
            } else if explicitly_requested {
                safe_eprintln!("c Error: --verify-proof could not be fulfilled: {reason}");
            } else {
                safe_eprintln!("c Warning: automatic proof verification skipped: {reason}");
            }
            let accepted = verification_skip_is_acceptable(explicitly_requested);
            if !accepted {
                cleanup_temp_proof_file(proof);
            }
            accepted
        }
        VerifyOutcome::Rejected { reason } => {
            if optional_default {
                safe_eprintln!(
                    "c Warning: automatic proof verification failed for {}: {reason}",
                    proof.path
                );
                if let Err(error) = remove_owned_dimacs_proof(&proof.path) {
                    safe_eprintln!(
                        "c Warning: failed to remove rejected optional DIMACS proof {}: {error}",
                        proof.path
                    );
                }
                return false;
            }
            safe_eprintln!(
                "c Error: proof verification FAILED for {} — {reason}",
                proof.path
            );
            safe_eprintln!(
                "c Error: SOUNDNESS FAILURE — solver reported UNSAT but emitted proof was rejected by internal checker"
            );
            // Leave the proof file on disk when it was user-requested, so
            // the user can re-run drat-trim / lrat-check to diagnose.
            // Remove it if we synthesized it (no user requested it).
            cleanup_temp_proof_file(proof);
            let _ = io::stdout().flush();
            let _ = io::stderr().flush();
            false
        }
    }
}

#[must_use]
fn verify_unsat_proof_from_source(
    source: DimacsInputSource<'_>,
    proof_config: Option<&ProofConfig>,
) -> bool {
    if !super::VERIFY_PROOF_ENABLED.load(Ordering::SeqCst) {
        return true;
    }

    match source {
        DimacsInputSource::Content(content) => verify_unsat_proof(content, proof_config),
        DimacsInputSource::FilePath { path, sha256 } => {
            let content = match read_authenticated_dimacs_source(path, sha256) {
                Ok(content) => content,
                Err(error) => {
                    let optional_default =
                        proof_config.is_some_and(synthesized_default_dimacs_proof_is_optional);
                    if optional_default {
                        safe_eprintln!(
                            "c Warning: automatic proof verification skipped changed or unreadable DIMACS input {path}: {error}"
                        );
                    } else {
                        safe_eprintln!(
                            "c Error: verify-proof refused changed or unreadable DIMACS input {path}: {error}"
                        );
                    }
                    if let Some(proof) = proof_config {
                        cleanup_temp_proof_file(proof);
                    }
                    return false;
                }
            };
            verify_unsat_proof(&content, proof_config)
        }
        DimacsInputSource::Unavailable => {
            let explicitly_requested = super::EXPLICIT_VERIFY_PROOF_ENABLED.load(Ordering::SeqCst);
            if explicitly_requested {
                safe_eprintln!(
                    "c Error: --verify-proof cannot verify streamed input whose original bytes are unavailable"
                );
            } else {
                safe_eprintln!(
                    "c Warning: automatic proof verification skipped: original DIMACS content unavailable for streamed input"
                );
            }
            if let Some(proof) = proof_config {
                cleanup_temp_proof_file(proof);
            }
            verification_skip_is_acceptable(explicitly_requested)
        }
    }
}
