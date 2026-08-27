// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Proof writer accessors.
//!
//! The bulk of result declaration logic is in sibling modules:
//! - `finalize_unsat`: UNSAT declaration and proof finalization
//! - `finalize_sat`: SAT model reconstruction, verification, and result shaping
//! - `ext_conflict`: Extension/theory conflict postprocessing

use super::super::*;

#[cfg(test)]
std::thread_local! {
    static FMLA_LEARNED_LRAT_DRY_RUN_ARTIFACT_HOOK_CALLS: std::cell::Cell<u64> =
        const { std::cell::Cell::new(0) };
}

impl Solver {
    #[cfg(test)]
    pub(crate) fn reset_fmla_learned_lrat_dry_run_artifact_hook_calls() {
        FMLA_LEARNED_LRAT_DRY_RUN_ARTIFACT_HOOK_CALLS.with(|calls| calls.set(0));
    }

    #[cfg(test)]
    pub(crate) fn fmla_learned_lrat_dry_run_artifact_hook_calls() -> u64 {
        FMLA_LEARNED_LRAT_DRY_RUN_ARTIFACT_HOOK_CALLS.with(std::cell::Cell::get)
    }

    /// Get the proof writer (for testing/inspection)
    pub fn proof_writer(&self) -> Option<&ProofOutput> {
        self.proof_manager.as_ref().map(ProofManager::output)
    }

    /// Flush the attached proof output without exposing mutable format authority.
    ///
    /// Returns `Ok(true)` when an output was attached and flushed, or
    /// `Ok(false)` when the solver has no proof output.
    ///
    /// # Errors
    ///
    /// Returns the attached writer's I/O error if flushing fails.
    pub fn flush_proof_writer(&mut self) -> std::io::Result<bool> {
        let Some(manager) = self.proof_manager.as_mut() else {
            return Ok(false);
        };
        manager.flush()?;
        Ok(true)
    }

    /// Detach the proof output from the solver.
    ///
    /// Explicit internal LRAT and live clause-trace consumers remain active.
    /// Detaching the last consumer transitions conservatively to no-proof
    /// state without restoring a stale pre-proof control snapshot.
    pub fn take_proof_writer(&mut self) -> Option<ProofOutput> {
        self.maybe_write_fmla_learned_lrat_dry_run_proof_artifact_from_env();
        self.detach_proof_writer()
    }

    /// Detach proof output without consulting ambient artifact-export env vars.
    ///
    /// Remaining internal LRAT or clause-trace ownership is preserved exactly
    /// as by [`Self::take_proof_writer`].
    pub(crate) fn take_proof_writer_without_artifact(&mut self) -> Option<ProofOutput> {
        self.detach_proof_writer()
    }

    /// Export checker-visible Fmla learned-LRAT dry-run rows to a retained JSON artifact.
    ///
    /// This is evidence-only: the exported envelope still requires same-run
    /// post-check replay before it can authorize Main `proof.out`.
    pub fn write_fmla_learned_lrat_dry_run_proof_artifact_json(
        &self,
        path: impl AsRef<std::path::Path>,
    ) -> std::io::Result<Option<std::path::PathBuf>> {
        let path = path.as_ref();
        let artifact = self.select_fmla_learned_lrat_dry_run_proof_artifact();
        let envelope = ProofManager::export_fmla_learned_lrat_dry_run_proof_artifact(&artifact);
        let payload = ProofManager::fmla_learned_lrat_dry_run_proof_artifact_envelope_to_json_value(
            &envelope,
        );

        if let Some(parent) = path
            .parent()
            .filter(|parent| !parent.as_os_str().is_empty())
        {
            std::fs::create_dir_all(parent)?;
        }
        let mut bytes = serde_json::to_vec_pretty(&payload)
            .map_err(|err| std::io::Error::new(std::io::ErrorKind::InvalidData, err))?;
        bytes.push(b'\n');
        // Write atomically: serialize to a unique temp file in the same
        // directory, then rename into place. The destination is a process-global
        // path (set via FMLA_LEARNED_LRAT_DRY_RUN_PROOF_ARTIFACT_PATH_ENV), so
        // multiple solver finalizations can target it concurrently. A plain
        // truncate-then-write lets a concurrent reader observe a zero-length file
        // mid-write (seen as flaky "EOF while parsing a value" artifact reads);
        // rename(2) is atomic within a filesystem, so readers always see a
        // complete artifact — never a partial one.
        use std::sync::atomic::{AtomicU64, Ordering};
        static ARTIFACT_TMP_SEQ: AtomicU64 = AtomicU64::new(0);
        let seq = ARTIFACT_TMP_SEQ.fetch_add(1, Ordering::Relaxed);
        let mut tmp_os = path.as_os_str().to_owned();
        tmp_os.push(format!(".tmp.{}.{}", std::process::id(), seq));
        let tmp_path = std::path::PathBuf::from(tmp_os);
        std::fs::write(&tmp_path, &bytes)?;
        if let Err(err) = std::fs::rename(&tmp_path, path) {
            let _ = std::fs::remove_file(&tmp_path);
            return Err(err);
        }
        Ok(Some(path.to_path_buf()))
    }

    pub(super) fn maybe_write_fmla_learned_lrat_dry_run_proof_artifact_from_env(&self) {
        #[cfg(test)]
        FMLA_LEARNED_LRAT_DRY_RUN_ARTIFACT_HOOK_CALLS
            .with(|calls| calls.set(calls.get().saturating_add(1)));

        if !self.cold.ambient_artifacts_enabled {
            return;
        }
        let Ok(path) = std::env::var(
            crate::fmla_runtime_ledger::FMLA_LEARNED_LRAT_DRY_RUN_PROOF_ARTIFACT_PATH_ENV,
        ) else {
            return;
        };
        let path = path.trim();
        if path.is_empty() {
            return;
        }
        if let Err(err) = self.write_fmla_learned_lrat_dry_run_proof_artifact_json(path) {
            eprintln!(
                "warning: failed to write Fmla learned-LRAT dry-run artifact to {path}: {err}"
            );
        }
    }

    fn select_fmla_learned_lrat_dry_run_proof_artifact(
        &self,
    ) -> crate::proof_manager::LearnedLratDryRunProofArtifact {
        let learned = self.proof_manager.as_ref().and_then(|proof_manager| {
            Self::best_fmla_learned_lrat_dry_run_artifact(
                proof_manager.dry_run_fmla_learned_lrat_materialization_fragments(),
            )
        });
        let bounded_materializer = self.bounded_fmla_materializer_diagnostic_artifact();

        match (learned, bounded_materializer) {
            (Some(learned), Some(bounded_materializer)) => {
                let learned_priority =
                    Self::fmla_learned_lrat_dry_run_artifact_priority(&learned).unwrap_or(0);
                let bounded_priority =
                    Self::fmla_learned_lrat_dry_run_artifact_priority(&bounded_materializer)
                        .unwrap_or(0);
                if bounded_priority > learned_priority {
                    bounded_materializer
                } else {
                    learned
                }
            }
            (Some(learned), None) => learned,
            (None, Some(bounded_materializer)) => bounded_materializer,
            (None, None) => ProofManager::fail_closed_no_fmla_learned_lrat_dry_run_proof_artifact(),
        }
    }

    fn best_fmla_learned_lrat_dry_run_artifact(
        artifacts: Vec<crate::proof_manager::LearnedLratDryRunProofArtifact>,
    ) -> Option<crate::proof_manager::LearnedLratDryRunProofArtifact> {
        let mut best = None;
        let mut best_priority = 0;
        for artifact in artifacts {
            let Some(priority) = Self::fmla_learned_lrat_dry_run_artifact_priority(&artifact)
            else {
                continue;
            };
            if priority > best_priority {
                best_priority = priority;
                best = Some(artifact);
            }
        }
        best
    }

    fn bounded_fmla_materializer_diagnostic_artifact(
        &self,
    ) -> Option<crate::proof_manager::LearnedLratDryRunProofArtifact> {
        let stats = self.inproc.decompose_engine.lrat_preflight_stats();
        let checker_visible_id = stats.main_rewrite_materializer_first_reject_checker_visible_id;
        if stats.main_rewrite_materializer_fail_closed != 0 && checker_visible_id != 0 {
            if let Some(artifact) = self.proof_manager.as_ref().and_then(|proof_manager| {
                proof_manager
                    .fail_closed_fmla_materializer_rows_diagnostic_artifact(checker_visible_id)
            }) {
                return Some(artifact);
            }
            if let Some(artifact) = self
                .fmla_support_cover_sidecar_materializer_rows_diagnostic_artifact(
                    checker_visible_id,
                )
            {
                return Some(artifact);
            }
            Some(
                ProofManager::fail_closed_missing_fmla_materializer_dependency_artifact(
                    checker_visible_id,
                ),
            )
        } else {
            None
        }
    }

    fn fmla_support_cover_sidecar_materializer_rows_diagnostic_artifact(
        &self,
        checker_visible_id: u64,
    ) -> Option<crate::proof_manager::LearnedLratDryRunProofArtifact> {
        const MAX_SIDECAR_MATERIALIZER_ROWS: usize = 1024;

        let mut rows = Vec::new();
        for sidecar in self
            .inproc
            .decompose_engine
            .fmla_guarded_equiv_support_cover_lrat_sidecars()
            .iter()
        {
            if sidecar.planned_add_id == 0 || sidecar.lrat_hints.is_empty() {
                continue;
            }
            let mut hints = Vec::with_capacity(sidecar.lrat_hints.len());
            let mut seen = crate::kani_compat::det_hash_set_with_capacity(sidecar.lrat_hints.len());
            for &hint in &sidecar.lrat_hints {
                if hint != 0 && seen.insert(hint) {
                    hints.push(hint);
                }
            }
            if hints.is_empty() {
                continue;
            }
            rows.push(crate::proof_manager::LearnedLratReplayRow {
                kind: crate::proof_manager::LearnedLratReplayRowKind::MaterializerAdd,
                checker_visible_id: sidecar.planned_add_id,
                clause_lits_dimacs: sidecar.clause_lits_dimacs.clone(),
                checker_visible_lrat_hints: hints,
            });
            if rows.len() >= MAX_SIDECAR_MATERIALIZER_ROWS {
                break;
            }
        }

        if rows.is_empty() {
            return None;
        }

        let replay = crate::proof_manager::LearnedLratMaterializationReplay {
            checker_visible_id,
            materialization_status:
                crate::proof_manager::LearnedLratMaterializationStatus::FailClosedNoLearnedLratAuthorityRecords,
            rows,
            proof_out_emitted: false,
            proof_writer_io_error: false,
        };
        Some(ProofManager::dry_run_fmla_learned_lrat_materialization_fragment_from_replay(&replay))
    }

    fn fmla_learned_lrat_dry_run_artifact_priority(
        artifact: &crate::proof_manager::LearnedLratDryRunProofArtifact,
    ) -> Option<u16> {
        use crate::proof_manager::LearnedLratMaterializationStatus as Status;

        if artifact.authorizes_main_proof_out || artifact.external_checker_verified {
            return None;
        }

        // Ranking: complete learned fragment > learned fail-closed diagnostic >
        // materializer-row diagnostic > empty no-record fallback.
        let base = match artifact.materialization_status {
            Status::RetainedDependenciesComplete => {
                if artifact.external_checker_required
                    && !artifact.proof_out_emitted
                    && !artifact.proof_writer_io_error
                    && !artifact.rows.is_empty()
                    && !artifact.lrat_fragment.is_empty()
                {
                    100
                } else {
                    return None;
                }
            }
            Status::FailClosedIncompleteLearnedDependency => 80,
            Status::FailClosedIncompleteMaterializerDependency => 70,
            Status::FailClosedMalformedReplayRows => 60,
            Status::FailClosedMissingMaterializerDependency => 50,
            Status::FailClosedProofWriterIoError => 40,
            Status::FailClosedProofOutAlreadyEmitted => 30,
            Status::FailClosedNoLearnedLratAuthorityRecords => {
                if artifact.rows.is_empty() {
                    10
                } else if artifact.lrat_fragment.is_empty() {
                    return None;
                } else {
                    20
                }
            }
        };

        if artifact.materialization_status != Status::RetainedDependenciesComplete
            && artifact.external_checker_required
        {
            return None;
        }

        Some(base + u16::from(artifact.checker_visible_id != 0))
    }
}
