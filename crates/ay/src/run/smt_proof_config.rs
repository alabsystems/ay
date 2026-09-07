// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `run` to keep SMT proof-config lifecycle helpers in
// the execution module's private namespace.

/// Adapt a proof config for the SMT-LIB execution path.
///
/// When default proof auto-verification synthesizes a temporary DRAT path, the
/// choice happens before the input format is known. SMT-LIB produces Alethe,
/// which AY cannot post-check with its DRAT/LRAT verifier. Such verify-only temp
/// configs are therefore dropped instead of enabling costly proof tracking,
/// writing Alethe, and deleting it without verification. An explicit
/// `--verify-proof` is rejected by the route gate before this adapter runs.
///
/// A SYNTHESIZED DEFAULT is likewise dropped while the proof cycle is shed
/// (`PROOF_CYCLE_SHED_ENABLED`: a plain solve, `--no-proof`, `--z3-mode`,
/// competition mode). A shedding executor records no proof, so the artifact
/// could never be rendered, and handing the config to `configure_proof_policy`
/// would call `set_best_effort_produce_proofs` and silently re-arm the tracker
/// for a sidecar nobody asked for. `build_proof_config` still synthesizes the
/// default for every `.smt2` input because the CHC runner retargets it to
/// `<input>.chccert`; only the SMT decision route sheds it.
///
/// Returns `None` when `proof_config` is `None`, verify-only temporary, or a
/// synthesized default under shedding. Explicit proof configs are returned
/// unchanged; the caller validates that their format is Alethe.
fn adapt_proof_config_for_smt(proof_config: Option<&ProofConfig>) -> Option<ProofConfig> {
    let src = proof_config?;
    if src.is_temp {
        return None;
    }
    if src.synthesized_default && PROOF_CYCLE_SHED_ENABLED.load(std::sync::atomic::Ordering::SeqCst)
    {
        return None;
    }
    Some(src.clone())
}

fn logic_from_commands(commands: &[Command]) -> Option<&str> {
    commands.iter().find_map(|command| {
        if let Command::SetLogic(logic) = command {
            Some(logic.as_str())
        } else {
            None
        }
    })
}

/// Remove a synthesized temp proof file after the SMT run completes.
/// No-op when the config is `None`, not marked `is_temp`, or the file is
/// already absent. Used to avoid leaving stray `/tmp/ay-verify-*.alethe`
/// files when `--verify-proof` auto-defaults on under debug builds with
/// no user-supplied `--proof` path (Finding A).
fn cleanup_temp_proof(proof_config: Option<&ProofConfig>) {
    if let Some(proof) = proof_config {
        if proof.is_temp {
            let _ = std::fs::remove_file(&proof.path);
        }
    }
}
