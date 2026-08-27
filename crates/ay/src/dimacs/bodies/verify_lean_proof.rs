// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

fn run_authenticated_lean_verifier(
    snapshot: &AuthenticatedLeanSnapshot,
) -> super::lean_verify::LeanVerificationOutcome {
    let mut verifier = super::lean_verify::LeanVerifier::new();
    if let Some(path) = super::LEAN_BINARY_PATH.get() {
        verifier = verifier.with_path(path);
    }
    #[cfg(target_os = "linux")]
    return verifier.verify_descriptor(&snapshot.descriptor);
    #[cfg(not(target_os = "linux"))]
    super::lean_verify::LeanVerificationOutcome::Unavailable {
        reason: "Lean verification requires a re-openable authenticated anonymous descriptor path, which is unavailable on this platform".to_string(),
    }
}

fn verify_lean_proof_body(proof_config: Option<&ProofConfig>) -> bool {
    if !super::LEAN_VERIFY_ENABLED.load(Ordering::SeqCst) {
        return true;
    }
    let proof = match proof_config {
        Some(p) => p,
        None => {
            safe_eprintln!("c Error: --lean-verify set but no proof was emitted");
            return false;
        }
    };
    if proof.format != ProofFormat::Lean4 {
        safe_eprintln!(
            "c Error: --lean-verify requires a Lean4 proof (.lean4 or --proof-format lean4); got {:?}",
            proof.format
        );
        return false;
    }
    let published = match validate_published_dimacs_proof(&proof.path) {
        Ok(published) => published,
        Err(error) => {
            safe_eprintln!(
                "c Error: Lean verification refused unauthenticated proof {}: {error}",
                proof.path
            );
            return false;
        }
    };
    let mut snapshot = match AuthenticatedLeanSnapshot::create(&proof.path, published) {
        Ok(snapshot) => snapshot,
        Err(error) => {
            safe_eprintln!(
                "c Error: failed to create authenticated Lean snapshot for {}: {error}",
                proof.path
            );
            return false;
        }
    };
    if let Err(error) = snapshot.validate() {
        safe_eprintln!(
            "c Error: authenticated Lean snapshot for {} failed validation: {error}",
            proof.path
        );
        return false;
    }

    // Lean sees only the anonymous digest-bound snapshot. The inherited
    // descriptor pins the exact inode across exec; the public proof path
    // remains useful as a retained artifact, but it is never a verifier input.
    let outcome = run_authenticated_lean_verifier(&snapshot);
    if let Err(error) = snapshot.validate() {
        safe_eprintln!(
            "c Error: authenticated Lean snapshot for {} changed during kernel verification: {error}",
            proof.path
        );
        return false;
    }
    match outcome {
        super::lean_verify::LeanVerificationOutcome::Accepted => {
            if let Err(error) = validate_published_dimacs_proof(&proof.path) {
                safe_eprintln!(
                    "c Error: Lean proof {} changed during kernel verification: {error}",
                    proof.path
                );
                return false;
            }
            safe_eprintln!("c Lean verification: OK ({})", proof.path);
            true
        }
        super::lean_verify::LeanVerificationOutcome::Rejected {
            diagnostic,
            exit_code,
        } => {
            safe_eprintln!(
                "c Error: Lean kernel REJECTED proof {} (exit {exit_code})",
                proof.path
            );
            if !diagnostic.trim().is_empty() {
                safe_eprintln!("c Lean diagnostics:\n{diagnostic}");
            }
            safe_eprintln!(
                "c Error: SOUNDNESS FAILURE — solver reported UNSAT but emitted proof was rejected by Lean kernel"
            );
            let _ = io::stdout().flush();
            let _ = io::stderr().flush();
            false
        }
        super::lean_verify::LeanVerificationOutcome::Unavailable { reason } => {
            safe_eprintln!(
                "c Error: Lean verification unavailable: {reason} (the requested kernel check did not run)"
            );
            false
        }
    }
}
