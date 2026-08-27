// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

fn configure_dimacs_solver(solver: &mut SatSolver, _stats_cfg: stats_output::StatsConfig) {
    configure_dimacs_solver_body(solver);
}

// Serialize the process-global FMLA proof-out env override: the mutation and its
// restoration stay in one lock-scoped, panic-safe RAII guard (the toolchain's
// env_mutation lint prescription — mirrors deductive-checks-merge-contract's
// RUSTC_BOOTSTRAP pattern). Two concurrent solves can no longer race the
// variable or restore each other's values.
static FMLA_PROOF_OUT_ENV_LOCK: Mutex<()> = Mutex::new(());

struct FmlaCurrentProofOutEnvGuard {
    previous: Option<std::ffi::OsString>,
    _lock: std::sync::MutexGuard<'static, ()>,
}

impl FmlaCurrentProofOutEnvGuard {
    // Blessed env_mutation site: this IS the lock-scoped-helper pattern the
    // lint prescribes — an RAII guard that captures the previous value here
    // and restores it in Drop below; the CLI solve path holding it is
    // single-threaded with respect to this variable's readers.
    #[allow(unknown_lints, env_mutation)]
    fn set_for_proof(proof_config: Option<&ProofConfig>) -> Self {
        let lock = FMLA_PROOF_OUT_ENV_LOCK
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let previous = std::env::var_os(
            ay_sat::fmla_runtime_ledger::FMLA_LEARNED_LRAT_CURRENT_PROOF_OUT_PATH_ENV,
        );
        if let Some(proof) = proof_config {
            std::env::set_var(
                ay_sat::fmla_runtime_ledger::FMLA_LEARNED_LRAT_CURRENT_PROOF_OUT_PATH_ENV,
                &proof.path,
            );
        } else {
            std::env::remove_var(
                ay_sat::fmla_runtime_ledger::FMLA_LEARNED_LRAT_CURRENT_PROOF_OUT_PATH_ENV,
            );
        }
        Self {
            previous,
            _lock: lock,
        }
    }
}

impl Drop for FmlaCurrentProofOutEnvGuard {
    // Blessed env_mutation site: restore arm of the RAII guard above.
    #[allow(unknown_lints, env_mutation)]
    fn drop(&mut self) {
        if let Some(previous) = self.previous.take() {
            std::env::set_var(
                ay_sat::fmla_runtime_ledger::FMLA_LEARNED_LRAT_CURRENT_PROOF_OUT_PATH_ENV,
                previous,
            );
        } else {
            std::env::remove_var(
                ay_sat::fmla_runtime_ledger::FMLA_LEARNED_LRAT_CURRENT_PROOF_OUT_PATH_ENV,
            );
        }
    }
}
