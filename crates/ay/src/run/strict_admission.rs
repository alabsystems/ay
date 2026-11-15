// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `run`: the `--strict-proofs` admission decision, made
// ONCE, where a decision query's `unsat` is published.
//
// `--strict-proofs` promises `unsat` only together with a certificate that
// proves it: no unproved (`hole`/`trust`) step and no `assume` the problem
// does not state. That promise used to be checked only inside
// `write_alethe_proof`, i.e. only when AY wrote a certificate FILE. Every other
// route published the verdict on the in-memory screen alone, which cannot see
// a step the printer downgrades to `hole`. Measured on the round-4 head over
// the 79 files the file gate withheld: `--strict-proofs --stdin`,
// `--incremental --strict-proofs` and `--strict-proofs --no-proof F`, each with
// `(get-proof)` appended, published `unsat` on 76 of 76 single-query files and
// printed a proof carrying `:rule hole`/`trust` for every one; plain
// `--strict-proofs --stdin` published `unsat` on all 79 with no certificate at
// all.
//
// The decision now reads the DOCUMENT on every route: the proof is rendered
// through the same problem-scoped exporter `(get-proof)` and the certificate
// file use, into a scanner that keeps no text except the `assume` leaves, and
// the verdict is admitted only when that document is complete and every
// premise it assumes is one the problem states verbatim. The file route keeps
// its own check on the bytes it actually wrote (`strict_certificate_withheld`),
// which now reads the same scanner, so the two can only disagree if the
// exporter is not deterministic — and then the file route still refuses.

/// Whether the `unsat` this executor is about to publish is under strict
/// proofs: `--strict-proofs` (`--rigor strict`) on the command line, or
/// `(set-option :check-proofs-strict true)` in the script. The two spellings
/// are ONE admission decision on the published document. The executor's own
/// funnel for the in-script option judges only the in-memory derivation, and
/// cannot see a step the Alethe printer downgrades to `hole`: measured on the
/// round-5 head, a script that set the option published `unsat` and then
/// printed `:rule hole` from `(get-proof)`.
///
/// This is the LIVE read of the executor's option table. A decision query's
/// strict request is recorded once, when the query starts
/// (`SmtTranscriptState::query_strict_proofs_requested`), and every gate below
/// takes that recorded request as its `strict` argument: an option set after a
/// `check-sat` applies to later queries only, so a gate that re-read the live
/// option when the query's certificate is published at EOF would judge the
/// query under a request it was not answered under.
fn strict_admission_requested(executor: &Executor) -> bool {
    crate::strict_request::strict_proofs_requested(executor.script_strict_proofs_requested())
}

/// The in-memory half of the strict decision: strict was requested for this
/// query (`strict`) and the retained derivation has a `trust`/`hole` step on
/// its path to `(cl)`.
fn strict_derivation_screen_refuses(strict: bool, executor: &Executor) -> bool {
    strict && terminal_trust_detected(executor)
}

// The streaming document reader, shared with the executor's own publication
// gates (`ay_proof::AletheDocumentScan`).
use ay_proof::AletheDocumentScan;

/// Whether every premise a document assumes is one the problem states.
#[derive(Debug, Clone, PartialEq, Eq)]
enum AssumedPremises {
    /// Every top-level `assume` is, token for token, an authored premise.
    Verbatim,
    /// This `assume` is not a premise the problem states.
    Foreign(String),
    /// The comparison could not be made: the authored syntax of some
    /// assertion is not retained, or the scan overflowed.
    Unjudged(&'static str),
}

fn assumed_premises(executor: &Executor, scan: &AletheDocumentScan) -> AssumedPremises {
    if scan.overflowed {
        return AssumedPremises::Unjudged("the document's assume leaves exceed the scan bound");
    }
    let Some(authored) = executor.authored_premise_surfaces() else {
        return AssumedPremises::Unjudged("an assertion's authored syntax was not retained");
    };
    let shown = |assume: &str| {
        let mut shown = assume.to_string();
        if shown.len() > 200 {
            let mut cut = 200;
            while !shown.is_char_boundary(cut) {
                cut -= 1;
            }
            shown.truncate(cut);
            shown.push('…');
        }
        shown
    };
    for assume in &scan.premise_assumes {
        if !authored.contains(&ay_dpll::normalize_premise_surface(assume)) {
            return AssumedPremises::Foreign(shown(assume.as_str()));
        }
    }
    // Verbatim up to spelling, but not to pinned Carcara's sorts: in a logic
    // with reals and no integers it reads the problem's numerals as `Real`s
    // and the certificate's as `Int`s, and a `let` variable bound to such a
    // term has a different sort on the two sides
    // (`ay_dpll::premise_int_let_binding`).
    if executor.authored_numerals_read_as_reals() {
        for assume in &scan.premise_assumes {
            if let Some(binder) = ay_dpll::premise_int_let_binding(assume) {
                return AssumedPremises::Foreign(format!(
                    "{}; the logic has no Int sort, so pinned Carcara reads the `let` variable `{binder}` as a Real in the problem but as an Int in this `assume`, where its value is a numeral term",
                    shown(assume.as_str())
                ));
            }
        }
    }
    AssumedPremises::Verbatim
}

/// Why `--strict-proofs` withholds a computed `unsat`, with the typed reason
/// the transcript publishes beside `unknown`.
struct StrictRefusal {
    reason: &'static str,
    detail: String,
}

/// The document half of the strict admission decision for the query whose
/// `unsat` is about to be published, or `None` when strict may publish it.
///
/// Runs after the in-memory screen (`terminal_trust_detected`), which it does
/// not replace: that screen reads the derivation, this reads what a strict
/// consumer receives.
fn strict_document_refusal(
    strict: bool,
    executor: &Executor,
    output: &str,
) -> Option<StrictRefusal> {
    if output != "unsat" || !strict {
        return None;
    }
    if executor.last_proof().is_none() {
        return Some(StrictRefusal {
            reason: "(incomplete proof-unavailable)",
            detail: "strict proof mode rejected UNSAT because no derivation was retained for it"
                .to_string(),
        });
    }
    let mut scan = AletheDocumentScan::default();
    match executor.try_export_last_proof_alethe_for_problem_scope_to(&mut scan) {
        Some(Ok(())) => {}
        Some(Err(error)) => {
            return Some(StrictRefusal {
                reason: "(incomplete proof-unrenderable)",
                detail: format!(
                    "strict proof mode rejected UNSAT because proof rendering failed: {error}"
                ),
            });
        }
        None => {
            return Some(StrictRefusal {
                reason: "(incomplete proof-unavailable)",
                detail:
                    "strict proof mode rejected UNSAT because the proof export produced no document"
                        .to_string(),
            });
        }
    }
    strict_scan_refusal(executor, &scan, "its certificate")
}

/// The refusal for a scanned document, shared by every route.
fn strict_scan_refusal(
    executor: &Executor,
    scan: &AletheDocumentScan,
    what: &str,
) -> Option<StrictRefusal> {
    if scan.unproved > 0 {
        return Some(StrictRefusal {
            reason: "(incomplete proof-trusted)",
            detail: format!(
                "strict proof mode rejected UNSAT because {what} carries {} unproved step(s)",
                scan.unproved
            ),
        });
    }
    match assumed_premises(executor, scan) {
        AssumedPremises::Verbatim => None,
        AssumedPremises::Foreign(assume) => Some(StrictRefusal {
            reason: "(incomplete proof-trusted)",
            detail: format!(
                "strict proof mode rejected UNSAT because {what} assumes `{assume}`, which is not an assertion of the input as written"
            ),
        }),
        AssumedPremises::Unjudged(why) => Some(StrictRefusal {
            reason: "(incomplete proof-trusted)",
            detail: format!(
                "strict proof mode rejected UNSAT because the premises {what} assumes could not be compared with the input: {why}"
            ),
        }),
    }
}

/// Publish a document refusal exactly as the file route publishes one:
/// `unknown` with the typed reason, the decision trace invalidated, and the
/// refusal named on a `c strict-proofs:` line.
fn publish_strict_document_rejection(
    transcript: &mut SmtTranscriptState,
    cmd: &Command,
    executor: &mut Executor,
    refusal: StrictRefusal,
) -> bool {
    let downgraded = executor.reject_last_unsat_as_unknown();
    debug_assert!(downgraded, "strict document gate started from UNSAT");
    update_transcript_state_after_command(transcript, cmd);
    transcript.reject_result_certification(refusal.reason);
    invalidate_artifacts_for_rejected_result();
    if let Err(error) = invalidate_decision_trace_for_public_mismatch(transcript) {
        eprintln_smt_error(error);
        return false;
    }
    let published = print_synthesized_public_unknown(transcript);
    if published {
        print_diagnostic_line(transcript, &format!("c strict-proofs: {}", refusal.detail));
    }
    published
}

/// What a published Alethe certificate carries, read once for both the
/// `c ay.proof.certificate` disclosure and the strict publication gate, so the
/// two can never disagree about the same document.
struct CertificateEvidence {
    /// Unproved steps: the larger of the printed count and the in-memory one.
    unproved: u32,
    /// Whether the document's premise `assume`s are the problem's own.
    premises: AssumedPremises,
    /// The in-memory derivation has no `trust`/`hole` step on its path.
    derivation_trust_free: bool,
}

/// Read the document actually written to `path`.
///
/// The internal [`ay_proof::terminal_trust_report`] counts only `AletheRule::
/// Trust`, `AletheRule::Hole` and trust-kind theory lemmas on the in-memory
/// proof. The PRINTER independently downgrades any rule with no checkable
/// Alethe counterpart to the wire name `hole` at print time, and the report
/// never sees those. The document is what the external checker reads, so the
/// document is what gets counted — and what gets compared with the input.
fn certificate_evidence(executor: &Executor, path: &str) -> CertificateEvidence {
    let report = executor
        .last_proof()
        .map(ay_proof::terminal_trust_report)
        .unwrap_or_default();
    let internal_unproved = report
        .trust_rule_on_path
        .saturating_add(report.trust_theory_lemma_on_path)
        .saturating_add(report.hole_rule_on_path);
    let scan = AletheDocumentScan::of_file(path);
    // Take the larger of the two: the printed count catches print-time
    // downgrades the internal report cannot see, and the internal count catches
    // anything the textual scan would miss.
    let unproved = scan.as_ref().map_or(internal_unproved, |scan| {
        scan.unproved.max(internal_unproved)
    });
    // Two detectors, because each is blind where the other sees.
    // `unsat_proof_terminal_foreign_assume` judges the TERMS AY stores; it
    // catches a laundered axiom but cannot see a normalized spelling of a real
    // premise, since the stored term is already normalized. The document scan
    // compares each printed premise `assume` with the problem's assertions AS
    // WRITTEN: measured on the round-4 head, every certificate in every sweep
    // said `foreign_assumes=no` while the external checker rejected 10 of them
    // at an `assume` ("could not match term to any of the original problem
    // premises": `distinct` respelled as `not =`, a `define-fun` expanded, a
    // bit-vector literal respelled).
    let premises = if executor.unsat_proof_terminal_foreign_assume() {
        AssumedPremises::Foreign("a premise AY's provenance does not back".to_string())
    } else {
        match &scan {
            Some(scan) => assumed_premises(executor, scan),
            None => AssumedPremises::Unjudged("the written certificate could not be read back"),
        }
    };
    CertificateEvidence {
        unproved,
        premises,
        derivation_trust_free: report.is_trust_free(),
    }
}

/// The strict publication gate's refusal, or `None` when strict mode may
/// publish the certificate at `path`.
///
/// The same decision `strict_document_refusal` made when the verdict was
/// computed, re-taken on the bytes actually written: no unproved step, and
/// every premise `assume` an assertion of the input as written.
///
/// Deliberately NOT the library's `:check-proofs-strict` funnel. Its known-wire-
/// gap arm is a conservative PREDICTION of the printer; measured over 984
/// benchmark files, routing this flag through it withheld 33 further `unsat`s
/// whose certificates carry `unproved_steps=0 foreign_assumes=no` (3 of them
/// replay as valid in the external checker), on top of the 62 this gate
/// withheld.
fn strict_certificate_refusal(evidence: &CertificateEvidence, path: &str) -> Option<String> {
    if evidence.unproved > 0 {
        return Some(format!(
            "strict proof mode rejected UNSAT because its certificate {path} carries {} unproved step(s)",
            evidence.unproved
        ));
    }
    match &evidence.premises {
        AssumedPremises::Verbatim => None,
        AssumedPremises::Foreign(assume) => Some(format!(
            "strict proof mode rejected UNSAT because its certificate {path} assumes `{assume}`, which is not an assertion of the input as written"
        )),
        AssumedPremises::Unjudged(why) => Some(format!(
            "strict proof mode rejected UNSAT because the premises its certificate {path} assumes could not be compared with the input: {why}"
        )),
    }
}

/// STRICT PUBLICATION GATE. Under `--strict-proofs` the certificate is part of
/// the answer: an `unsat` whose document carries an unproved step or an
/// `assume` the input does not state is withheld, for an explicit `--proof`
/// exactly as for the synthesized default. The document is already at its
/// pathname, so its exact inode is invalidated; the pathname itself is never
/// removed (see `SmtUnsatPublicationTransaction`).
fn strict_certificate_withheld(
    strict: bool,
    executor: &Executor,
    proof_config: &ProofConfig,
    proof_file: &std::fs::File,
) -> Option<AletheProofPublication> {
    if !strict {
        return None;
    }
    let evidence = certificate_evidence(executor, &proof_config.path);
    let refusal = strict_certificate_refusal(&evidence, &proof_config.path)?;
    disclose_refused_artifact("strict", &proof_config.path, &refusal);
    let invalidation = invalidate_smt_publication_members(proof_file, None);
    Some(AletheProofPublication::RejectToUnknown {
        reason: "(incomplete proof-trusted)".to_string(),
        diagnostic: format!("{refusal}{invalidation}"),
    })
}
