// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Certified publication of a ground-first refutation (the fallback slot of
//! `check_sat/ground_first.rs`).
//!
//! # The document must state the problem's own premises
//!
//! The same-context probe decides the remainder as a standalone query over the
//! authored roots and their authored surfaces, so its proof build records the
//! source-syntax spellings (`last_proof_term_overrides`) that let the Alethe
//! printer `assume` each root exactly as the problem wrote it and bridge to
//! the canonical term the derivation uses. Installing the probe's PROOF
//! without those spellings printed the canonical term at the `assume`:
//! measured on `(assert (> x 5))`, the document read `(assume t0 (< 5 x))`,
//! AY's own certificate line said `foreign_assumes=yes ay_self_checkable=no`
//! beside `unsat_admission=strict-proof`, and carcara answered `invalid`
//! where the ordinary pipeline's document for the same file is `valid`
//! (verification report `2026-09-30-qe-ground-first-verify.md`, 2 green
//! certificates lost and 4 more invalid documents on the headline sample).
//!
//! The spellings therefore travel with the proof, and the installation is
//! kept only if the document it renders assumes nothing but the problem's own
//! assertions as written — the same comparison, over the same reference
//! (`Executor::authored_premise_surfaces`), that the CLI's certificate
//! disclosure and `--strict-proofs` publication gate make — and no terminal
//! trust, foreign `assume` or uncheckable surface reaches its empty clause.
//! Otherwise the installation is undone byte for byte and the refutation is
//! published on the sealed authored-subset theorem, which carries no document:
//! a seal without a document is weaker evidence than a valid certificate, but
//! an invalid certificate is no evidence at all.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::time::Instant;
use ay_core::{Proof, TermId};

use super::{duration_ms, Executor, MIN_BUDGET};
use crate::executor::normalize_premise_surface;
use crate::executor::quantifier_loop::result_mapping::{
    SameContextProbeOutcome, SameContextWindow,
};
use crate::executor_types::{SolveResult, Statistics};

/// Largest document the premise check renders. A remainder refutation larger
/// than this is published on the seal instead.
const MAX_CHECKED_DOCUMENT_BYTES: usize = 16 * 1024 * 1024;

/// A refutation of the remainder and the source-syntax spellings its proof
/// build recorded.
struct RemainderProof {
    proof: Proof,
    surface_overrides: Option<HashMap<TermId, String>>,
}

/// The proof state an installation writes, captured so a document that fails
/// the premise check can be withdrawn without a trace.
struct InstalledProofState {
    result: Option<SolveResult>,
    proof: Option<Proof>,
    quality: Option<ay_proof::ProofQuality>,
    check_result: Option<ay_proof::PartialProofCheck>,
    check_ok: bool,
    statistics: Statistics,
    reconstruction_suppressed: bool,
    surface_overrides: Option<HashMap<TermId, String>>,
}

impl InstalledProofState {
    fn capture(executor: &Executor) -> Self {
        Self {
            result: executor.last_result.clone(),
            proof: executor.last_proof.clone(),
            quality: executor.last_proof_quality.clone(),
            check_result: executor.proof_check_result.clone(),
            check_ok: executor.proof_check_ok,
            statistics: executor.last_statistics.clone(),
            reconstruction_suppressed: executor.last_unsat_proof_reconstruction_suppressed,
            surface_overrides: executor.last_proof_term_overrides.clone(),
        }
    }

    fn restore(self, executor: &mut Executor) {
        executor.last_result = self.result;
        executor.last_proof = self.proof;
        executor.last_proof_quality = self.quality;
        executor.proof_check_result = self.check_result;
        executor.proof_check_ok = self.check_ok;
        executor.last_statistics = self.statistics;
        executor.last_unsat_proof_reconstruction_suppressed = self.reconstruction_suppressed;
        executor.last_proof_term_overrides = self.surface_overrides;
    }
}

impl Executor {
    /// Publish the refutation of the authored roots at `subset` (whose roots
    /// are `remainder`) with evidence, by `deadline`: the ordinary proof of the
    /// remainder when its document states only the problem's premises,
    /// otherwise the sealed authored-subset theorem. `None` when neither
    /// route admits it.
    pub(super) fn ground_first_publish_certified(
        &mut self,
        subset: &[usize],
        remainder: &[TermId],
        deadline: Instant,
    ) -> Option<SolveResult> {
        // The document route may take half of the window, so a proof attempt
        // that does not complete still leaves the seal its share.
        let proof_deadline =
            Instant::now() + deadline.saturating_duration_since(Instant::now()) / 2;
        let until = |deadline: Instant| {
            let left = deadline.saturating_duration_since(Instant::now());
            (left >= MIN_BUDGET).then(|| duration_ms(left))
        };
        let proof_left = || until(proof_deadline);
        let left = || until(deadline);
        if let Some(candidate) = self.ground_first_remainder_proof(subset, remainder, &proof_left) {
            if self.install_authored_remainder_proof(candidate) {
                self.last_unknown_reason = None;
                return Some(SolveResult::unsat());
            }
        }
        let evidence =
            self.try_authorize_current_query_exact_authored_subset_unsat(subset, left()?)?;
        let result = self.emit_checked_exact_authored_subset_unsat(evidence);
        result.is_unsat().then_some(result)
    }

    /// The ordinary proof of the remainder: a same-context probe refutes
    /// exactly those authored roots, with their authored surfaces, through the
    /// whole pipeline (the goal's Skolemization and instances included).
    fn ground_first_remainder_proof(
        &mut self,
        subset: &[usize],
        remainder: &[TermId],
        left: &dyn Fn() -> Option<u64>,
    ) -> Option<RemainderProof> {
        // The authored surfaces of exactly these roots, when the host retains
        // them aligned with the (authored) window, so the probe sees the
        // remainder exactly as a standalone query would.
        let surfaces: Option<Vec<ay_frontend::command::Term>> = {
            let parsed = self.ctx.assertions_parsed();
            (parsed.len() == self.ctx.assertions.len()).then(|| {
                subset
                    .iter()
                    .map(|&position| parsed[position].clone())
                    .collect()
            })
        };
        let surfaces = surfaces.as_deref();
        let mut surface_overrides = None;
        let first = self.checked_same_context_unsat_proof(
            remainder,
            SameContextWindow::AuthoredRoots {
                surfaces,
                surface_overrides: &mut surface_overrides,
            },
            Some(left()?),
            None,
            true,
        );
        let proof = match first {
            SameContextProbeOutcome::Proof(proof) => proof,
            // The consequence replay's retry, for the same reason: a window
            // whose conflicts fused into lemmas the strict checker refuses may
            // complete with the whole-store array-axiom surface.
            SameContextProbeOutcome::UnsatUnpromotable => {
                match self.checked_same_context_unsat_proof(
                    remainder,
                    SameContextWindow::AuthoredRoots {
                        surfaces,
                        surface_overrides: &mut surface_overrides,
                    },
                    Some(left()?),
                    None,
                    false,
                ) {
                    SameContextProbeOutcome::Proof(proof) => proof,
                    _ => return None,
                }
            }
            SameContextProbeOutcome::Other => return None,
        };
        Some(RemainderProof {
            proof,
            surface_overrides,
        })
    }

    /// Install `candidate` through the shared authored-scope boundary and keep
    /// it only if its document states the problem's own premises (module
    /// docs); otherwise leave every byte of proof state as found.
    fn install_authored_remainder_proof(&mut self, candidate: RemainderProof) -> bool {
        let found = InstalledProofState::capture(self);
        self.last_proof_term_overrides = candidate.surface_overrides;
        if self.install_consequence_replay_candidate(Some(candidate.proof)) {
            // The document is the one this query would publish, which renders
            // only beside an UNSAT result (`Executor::last_proof`).
            self.last_result = Some(SolveResult::unsat());
            if self.installed_document_states_authored_premises() {
                return true;
            }
        }
        found.restore(self);
        false
    }

    /// Whether the installed proof renders to a document an external checker
    /// can match premise for premise: no terminal trust, foreign `assume` or
    /// uncheckable surface on its path to the empty clause, and every premise
    /// `assume` of the rendered document an authored assertion as written.
    /// A query that requested no proof output renders no document, so only
    /// the first condition applies to it.
    fn installed_document_states_authored_premises(&self) -> bool {
        if self.unsat_proof_terminal_trust_detected() {
            return false;
        }
        if self.last_proof().is_none() {
            return true;
        }
        let Some(authored) = self.authored_premise_surfaces() else {
            return false;
        };
        let mut scan = PremiseAssumeScan::default();
        if !matches!(
            self.try_export_last_proof_alethe_for_problem_scope_to(&mut scan),
            Some(Ok(()))
        ) || scan.overflowed
            || scan.depth != 0
        {
            return false;
        }
        scan.premises
            .iter()
            .all(|premise| authored.contains(&normalize_premise_surface(premise)))
    }
}

/// The premise `assume`s of a rendered Alethe document, read in one streaming
/// pass: every top-level `(assume ID TERM)` outside an `anchor` subproof (an
/// `assume` inside one is a local hypothesis, not a premise). The same reading
/// as the CLI's certificate scan.
#[derive(Default)]
struct PremiseAssumeScan {
    premises: Vec<String>,
    /// The document passed [`MAX_CHECKED_DOCUMENT_BYTES`]; nothing is judged.
    overflowed: bool,
    bytes: usize,
    depth: usize,
    in_string: bool,
    in_quoted_symbol: bool,
    /// The current top-level command.
    command: Vec<u8>,
    /// Open `anchor` subproofs, by the step id that closes them.
    anchors: Vec<String>,
}

impl PremiseAssumeScan {
    fn push(&mut self, byte: u8) {
        if self.depth > 0 {
            self.command.push(byte);
        }
        if self.in_string {
            self.in_string = byte != b'"';
            return;
        }
        if self.in_quoted_symbol {
            self.in_quoted_symbol = byte != b'|';
            return;
        }
        match byte {
            b'"' => self.in_string = true,
            b'|' => self.in_quoted_symbol = true,
            b'(' => {
                if self.depth == 0 {
                    self.command.clear();
                    self.command.push(byte);
                }
                self.depth += 1;
            }
            b')' => {
                self.depth = self.depth.saturating_sub(1);
                if self.depth == 0 {
                    self.finish_command();
                }
            }
            _ => {}
        }
    }

    fn finish_command(&mut self) {
        let text = String::from_utf8_lossy(&self.command);
        let Some(body) = text.strip_prefix('(').and_then(|t| t.strip_suffix(')')) else {
            self.overflowed = true;
            return;
        };
        let mut head = body.split_whitespace();
        match (head.next(), head.next(), head.next()) {
            (Some("anchor"), Some(":step"), Some(id)) => self.anchors.push(id.to_string()),
            (Some("step"), Some(id), _) if self.anchors.last().is_some_and(|open| open == id) => {
                self.anchors.pop();
            }
            (Some("assume"), Some(_), _) if self.anchors.is_empty() => {
                let term = body
                    .trim_start()
                    .strip_prefix("assume")
                    .map(str::trim_start)
                    .and_then(|rest| rest.split_once(char::is_whitespace))
                    .map(|(_id, term)| term.trim().to_string());
                match term {
                    Some(term) => self.premises.push(term),
                    None => self.overflowed = true,
                }
            }
            _ => {}
        }
    }
}

impl std::io::Write for PremiseAssumeScan {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        self.bytes = self.bytes.saturating_add(buf.len());
        if self.bytes > MAX_CHECKED_DOCUMENT_BYTES {
            self.overflowed = true;
            return Err(std::io::Error::other(
                "document exceeds the premise-check bound",
            ));
        }
        for &byte in buf {
            self.push(byte);
        }
        Ok(buf.len())
    }

    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::PremiseAssumeScan;
    use std::io::Write;

    fn premises(document: &str) -> (Vec<String>, bool) {
        let mut scan = PremiseAssumeScan::default();
        assert!(scan.write_all(document.as_bytes()).is_ok());
        (scan.premises, scan.overflowed || scan.depth != 0)
    }

    #[test]
    fn premise_assumes_are_read_outside_anchors_only() {
        let (found, failed) = premises(concat!(
            "(assume t0.a (> x 5))\n",
            "(step t0 (cl (< 5 x)) :rule resolution :premises (t0.a))\n",
            "(anchor :step t1 :args ((z Int)))\n",
            "(assume t1.h (= z |a b)|))\n",
            "(step t1 (cl) :rule subproof)\n",
            "(assume t2 (= s \"x)\"))\n",
        ));
        assert!(!failed);
        assert_eq!(found, vec!["(> x 5)", "(= s \"x)\")"]);
    }

    #[test]
    fn a_truncated_document_is_not_judged() {
        let (_, failed) = premises("(assume t0 (> x 5)");
        assert!(failed);
    }
}
