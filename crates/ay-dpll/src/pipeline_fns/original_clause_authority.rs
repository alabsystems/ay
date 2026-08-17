// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Original-clause proof-authority placement.
//!
//! The two ledgers (`clausification` / `theory`) are indexed by
//! `original_clause_id - 1` and tell [`crate::sat_proof_manager::SatProofManager`]
//! which Alethe rule authenticates each original clause in the SAT trace.
//!
//! # Why these functions never panic
//!
//! Placement runs deep inside the split-loop pipeline, on the *producer* side
//! of the proof pipeline. Every condition below used to be an `assert!` /
//! `expect` in production code: an ill-formed placement request aborted the
//! whole `check-sat` mid-solve, which is strictly worse than any verdict it
//! could have protected — it destroys the run rather than the row.
//!
//! `3b2d137b2` ("bind original authorities by stable clause id") introduced the
//! single-assignment assert; `c8ebc01c7` removed its then-live trigger (stale
//! ledgers surviving a SAT rebuild) but left the panic in place. The panic is
//! itself the defect: a re-placement that is legitimate must be allowed, and
//! one that is not must fail closed with a diagnostic that names the fix.
//!
//! # What "fail closed" means here
//!
//! Refusing to place, or retracting a contested slot, leaves the clause with
//! **no indexed authority**. `SatProofManager` then takes the anonymous
//! `assume` path for that original, `demote_non_problem_assumptions` turns a
//! non-assertion into an explicit `Trust` step, and mandatory strict
//! certification declines it. So the worst outcome of a refusal is an
//! `unknown`, never an unjustified `unsat`.
//!
//! Nor can a later placement launder a contested slot: the consumer
//! independently re-derives every annotation against the *traced* clause
//! (`canonicalize_tautology_clause` for clausification,
//! `rebind_theory_annotation` for theory lemmas) and falls back to the
//! anonymous path on any mismatch. The ledger proposes; it does not assert.

use std::sync::atomic::{AtomicBool, Ordering};

use ay_core::{ClausificationProof, TheoryLemmaProof};

/// Why a placement request could not be honored as written.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum AuthorityRefusal {
    /// Both a clausification and a theory annotation were offered for the same
    /// clause. One clause has one indexed authority; picking either silently
    /// would invent a provenance the producer did not state.
    TwoIndependentAuthorities,
    /// The target ID was never issued to an original (non-derived) clause.
    /// Derived IDs share the monotonic namespace, so this would bind a
    /// clausification rule onto a resolvent.
    IdNotIssuedAsOriginal,
    /// Original-clause IDs are one-based; `0` addresses no slot.
    IdIsZero,
    /// The ID does not fit the addressable ledger on this target.
    IdNotAddressable,
    /// A DIFFERENT authority is already resident at this ID. Both slots are
    /// retracted: neither producer's claim is trusted.
    ConflictingReplacement,
}

impl AuthorityRefusal {
    /// One-line statement of what went wrong.
    fn what(self) -> &'static str {
        match self {
            Self::TwoIndependentAuthorities => {
                "a clausification AND a theory authority were offered for one original clause"
            }
            Self::IdNotIssuedAsOriginal => {
                "the target clause ID was never issued to an original (non-derived) clause"
            }
            Self::IdIsZero => "the target clause ID is 0, but original-clause IDs are one-based",
            Self::IdNotAddressable => {
                "the target clause ID does not fit the addressable authority ledger"
            }
            Self::ConflictingReplacement => {
                "a different proof authority is already resident at this clause ID"
            }
        }
    }

    /// The options a producer has for fixing it. A refusal with no next step is
    /// a defect in its own right.
    fn how_to_fix(self) -> &'static str {
        match self {
            Self::TwoIndependentAuthorities => {
                "split the emission into two clauses, or drop the annotation that does not \
                 authenticate this clause's own rule"
            }
            Self::IdNotIssuedAsOriginal => {
                "capture `issued_original_clause_id_max()` immediately before the add and use \
                 `place_single_original_clause_authority`, or annotate the derived clause through \
                 the resolution-hint path instead"
            }
            Self::IdIsZero => {
                "read the ID back from the add that issued it rather than defaulting it"
            }
            Self::IdNotAddressable => {
                "this needs a 64-bit `usize` target, or an ID-keyed map in place of the dense \
                 ledger"
            }
            Self::ConflictingReplacement => {
                "clear the ledgers wherever the SAT solver is rebuilt (see \
                 `IncrementalTheoryState::fresh_sat_solver`), or record the authority once per \
                 issued ID instead of once per producer round"
            }
        }
    }
}

/// What a placement request did to the ledgers.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum AuthorityPlacement {
    /// Nothing was offered (both annotations `None`); the slot is untouched.
    Vacuous,
    /// The slot was empty and now carries the offered authority.
    Placed,
    /// The identical authority was already resident. Re-deriving the same
    /// clause by the same rule is LEGITIMATE and idempotent — the split loop
    /// legitimately revisits a clause across rounds — so this is not an error.
    Reaffirmed,
    /// The request was refused; the ledgers carry no authority for this ID.
    Refused(AuthorityRefusal),
}

/// Guards the stderr banner to one emission per process. Every refusal is
/// still reported in full through `tracing`; the banner exists so a producer
/// bug is visible in a bare test run, and one line is enough for that. There
/// is deliberately no env switch to silence it: a fail-closed report on an
/// internal defect is not a tuning knob.
static AUTHORITY_REFUSAL_BANNER_SHOWN: AtomicBool = AtomicBool::new(false);

fn report_authority_refusal(refusal: AuthorityRefusal, id: u64) {
    tracing::warn!(
        clause_id = id,
        refusal = ?refusal,
        what = refusal.what(),
        fix = refusal.how_to_fix(),
        "original-clause proof authority refused; failing closed to no authority for this clause"
    );
    if AUTHORITY_REFUSAL_BANNER_SHOWN.swap(true, Ordering::Relaxed) {
        return;
    }
    let what = refusal.what();
    let fix = refusal.how_to_fix();
    safe_eprintln!(
        "\n[AY PROOF AUTHORITY] refused a proof-authority placement for original clause \
         id={id}.\n    \
         what:   {what}\n    \
         effect: this clause now carries NO indexed authority. AY fail-closes it to an \
         uncertified step, so a derivation that needed it degrades to `unknown` (this is \
         SOUND); it indicates an internal solver bug worth reporting.\n    \
         fix:    {fix}\n    \
         (further refusals in this process are reported through `tracing` only)\n"
    );
}

/// Structural identity of two clausification annotations.
///
/// `ClausificationProof` carries no `PartialEq`; its two fields do, and they
/// are its whole content.
fn same_clausification(left: &ClausificationProof, right: &ClausificationProof) -> bool {
    left.rule == right.rule && left.source_term == right.source_term
}

/// Structural identity of two theory-lemma annotations.
fn same_theory_lemma(left: &TheoryLemmaProof, right: &TheoryLemmaProof) -> bool {
    left.clause == right.clause
        && left.kind == right.kind
        && left.farkas == right.farkas
        && left.lia == right.lia
}

/// Resize both original-clause authority ledgers to AY-SAT's actual issued-ID
/// high-water mark. The vectors are indexed by `clause_id - 1`, so gaps left
/// by derived clauses and omitted tautological originals must remain explicit
/// `None` slots rather than being compressed away.
///
/// A high-water mark that does not fit `usize` (32-bit targets only) leaves the
/// ledgers short rather than aborting: a short ledger reads back as `None`,
/// which is the fail-closed answer.
pub(crate) fn align_original_clause_authority_ledgers(
    solver: &ay_sat::Solver,
    clausification: &mut Vec<Option<ClausificationProof>>,
    theory: &mut Vec<Option<TheoryLemmaProof>>,
) {
    let Ok(len) = usize::try_from(solver.issued_original_clause_id_max()) else {
        return;
    };
    if clausification.len() < len {
        clausification.resize(len, None);
    }
    if theory.len() < len {
        theory.resize(len, None);
    }
}

/// Place authority for exactly one original clause issued after `before`.
///
/// Returns the issued ID on success. If the emission issued zero or multiple
/// original IDs (for example an oversized-clause split), all new slots stay
/// `None`: a single annotation cannot authenticate multiple trace identities.
pub(crate) fn place_single_original_clause_authority(
    solver: &ay_sat::Solver,
    before: u64,
    clausification_annotation: Option<ClausificationProof>,
    theory_annotation: Option<TheoryLemmaProof>,
    clausification: &mut Vec<Option<ClausificationProof>>,
    theory: &mut Vec<Option<TheoryLemmaProof>>,
) -> Option<u64> {
    let after = solver.issued_original_clause_id_max();
    align_original_clause_authority_ledgers(solver, clausification, theory);
    if after <= before {
        return None;
    }

    let mut issued = (before + 1..=after).filter(|&id| solver.is_issued_original_clause_id(id));
    let id = issued.next()?;
    if issued.next().is_some() {
        return None;
    }
    match place_original_clause_authority_at_id(
        solver,
        id,
        clausification_annotation,
        theory_annotation,
        clausification,
        theory,
    ) {
        AuthorityPlacement::Placed
        | AuthorityPlacement::Reaffirmed
        | AuthorityPlacement::Vacuous => Some(id),
        AuthorityPlacement::Refused(_) => None,
    }
}

/// Place authority at a known original-clause ID.
///
/// Authority is single-assignment *in content*: re-offering the identical
/// annotation is legitimate and idempotent, while offering a different one is a
/// producer bug. The bug is reported and the contested slot is retracted — it
/// is never panicked over, and the earlier proof is never silently overwritten.
pub(crate) fn place_original_clause_authority_at_id(
    solver: &ay_sat::Solver,
    id: u64,
    clausification_annotation: Option<ClausificationProof>,
    theory_annotation: Option<TheoryLemmaProof>,
    clausification: &mut Vec<Option<ClausificationProof>>,
    theory: &mut Vec<Option<TheoryLemmaProof>>,
) -> AuthorityPlacement {
    align_original_clause_authority_ledgers(solver, clausification, theory);
    let refuse = |refusal: AuthorityRefusal| {
        report_authority_refusal(refusal, id);
        AuthorityPlacement::Refused(refusal)
    };

    if clausification_annotation.is_none() && theory_annotation.is_none() {
        return AuthorityPlacement::Vacuous;
    }
    if clausification_annotation.is_some() && theory_annotation.is_some() {
        return refuse(AuthorityRefusal::TwoIndependentAuthorities);
    }
    if id == 0 {
        return refuse(AuthorityRefusal::IdIsZero);
    }
    if !solver.is_issued_original_clause_id(id) {
        return refuse(AuthorityRefusal::IdNotIssuedAsOriginal);
    }
    let Ok(index) = usize::try_from(id - 1) else {
        return refuse(AuthorityRefusal::IdNotAddressable);
    };
    // `align_*` sized both ledgers to the issued high-water mark, and `id` is
    // an issued original ID, so both slots exist. Bounds are still checked:
    // a caller with a stale solver handle must fail closed, not index-panic.
    if index >= clausification.len() || index >= theory.len() {
        return refuse(AuthorityRefusal::IdNotAddressable);
    }

    if clausification[index].is_none() && theory[index].is_none() {
        clausification[index] = clausification_annotation;
        theory[index] = theory_annotation;
        return AuthorityPlacement::Placed;
    }

    // The slot is occupied. Re-offering the SAME authority is a legitimate
    // re-derivation: the split loop revisits a clause across rounds, and the
    // producer re-states the rule it already stated.
    let reaffirms = match (
        clausification[index].as_ref(),
        theory[index].as_ref(),
        clausification_annotation.as_ref(),
        theory_annotation.as_ref(),
    ) {
        (Some(resident), None, Some(offered), None) => same_clausification(resident, offered),
        (None, Some(resident), None, Some(offered)) => same_theory_lemma(resident, offered),
        _ => false,
    };
    if reaffirms {
        return AuthorityPlacement::Reaffirmed;
    }

    // Two producers disagree about what authenticates this clause — including
    // the cross-kind case, where a theory lemma would displace a clausification
    // rule. Retract both slots so neither claim is trusted.
    clausification[index] = None;
    theory[index] = None;
    refuse(AuthorityRefusal::ConflictingReplacement)
}

pub(crate) fn drain_pending_original_clause_authorities(
    solver: &ay_sat::Solver,
    pending: &mut crate::incremental_proof_cache::IncrementalNegationCache,
    clausification: &mut Vec<Option<ClausificationProof>>,
    theory: &mut Vec<Option<TheoryLemmaProof>>,
) {
    use crate::incremental_proof_cache::PendingOriginalClauseAuthority;
    for authority in pending.drain_original_authorities() {
        let _ = match authority {
            PendingOriginalClauseAuthority::Clausification { original_id, proof } => {
                place_original_clause_authority_at_id(
                    solver,
                    original_id,
                    Some(proof),
                    None,
                    clausification,
                    theory,
                )
            }
            PendingOriginalClauseAuthority::Theory { original_id, proof } => {
                place_original_clause_authority_at_id(
                    solver,
                    original_id,
                    None,
                    Some(proof),
                    clausification,
                    theory,
                )
            }
        };
    }
    align_original_clause_authority_ledgers(solver, clausification, theory);
}

#[cfg(test)]
#[path = "original_clause_authority_tests.rs"]
mod tests;
