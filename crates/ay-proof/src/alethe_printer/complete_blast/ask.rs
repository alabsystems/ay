// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Who asks the complete bit-blast, and until when.
//!
//! Every other checked lowering answers the SUPPORT question "can the printer
//! spell this lemma?" by recognizing a shape. The complete bit-blast answers it
//! by building the answer: a bit-blast, a SAT refutation (direct, by cases,
//! swept, then monolithic) and a transport to text that is often tens of
//! megabytes. Asked from inside a solve, that answer must neither be paid where
//! no document can be read nor outlive the solve's own stop.
//!
//! Measured on `bv_affine_source`'s elaborated 64-bit constant multiples
//! (470d83f28 let the lane take the positive unit `(= L R)`): with no proofs
//! requested, the wire-gap screen asked it eight times; the eighth ask spent
//! the sweep's 120 s wall and then sat in the monolithic refutation, which
//! polled nothing, for over 50 minutes. Under a bare self-check
//! (`set_self_check` without proof collection) or `:check-proofs-strict`,
//! with a 20 s timeout, the same question ran past 100 s.
//!
//! A render asked from inside a solve (the wire-repair choice
//! `proof_renders_without_unproved_step`, the ground-closure screen
//! `renders_wire_clean`) is such a question too: it only judges a document.
//! It rendered through the exporter's [`CompleteBlastAsk::Asked`], which no
//! stop reaches; it now asks [`CompleteBlastAsk::AskedUntil`] with the
//! solve's stop (`try_export_alethe_with_authored_surfaces_within_solve`),
//! at both of the lane's entries, the unit refutation and the multi-literal
//! clause.
//! The render's work budget is not a stop for the lane: it counts the
//! printer's term spelling, which the bit-blast's search and transport do not
//! charge, and a spent budget already declines the lane before it blasts
//! (`complete_blast_surface_agrees`). The lane's own envelopes bound it.

use super::super::AlethePrinter;

/// Whether a support question may be answered through the complete bit-blast
/// (`format_bv_complete_blast_refutation`), and until when.
///
/// The exporter's document always renders [`Self::Asked`]. A decline here
/// leaves the conservative answer, an unproved step, which admits nothing.
/// Nothing about a stopped question is remembered (`bv_support_memo` keeps
/// only `true`, the refutation memo refutations), and of a declined one only
/// the monolithic refutation's counted refusal, which every mode meets alike
/// (`resolution_dag_memo/within.rs`), and, for the asking solve alone, its
/// screen's unstopped decline (`bv_support_memo/within_solve.rs`), which that
/// solve's own renders read too.
#[derive(Clone, Copy)]
pub enum CompleteBlastAsk<'s> {
    /// The lane answers exactly as the exporter renders, within its lanes'
    /// own envelopes.
    Asked,
    /// The lane answers as the exporter renders, but every refutation it runs
    /// polls `stop` and ends, unrefuted, once it returns `true`: the caller's
    /// own stop (an interrupt, the solve's certification deadline). It adds no
    /// budget; a stopped question is answered as a decline.
    AskedUntil(&'s dyn Fn() -> bool),
    /// No document can be observed: the lane declines before it blasts.
    NotAsked,
}

impl std::fmt::Debug for CompleteBlastAsk<'_> {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str(match self {
            Self::Asked => "Asked",
            Self::AskedUntil(_) => "AskedUntil(..)",
            Self::NotAsked => "NotAsked",
        })
    }
}

impl AlethePrinter<'_> {
    /// Why the complete bit-blast must not start, or `None` when it may.
    pub(super) fn complete_blast_unasked(&self) -> Option<&'static str> {
        match self.complete_blast {
            CompleteBlastAsk::NotAsked => Some("not asked: no Alethe document is observable"),
            _ if !self.complete_blast_keeps_going() => Some("the caller stopped the question"),
            CompleteBlastAsk::Asked | CompleteBlastAsk::AskedUntil(_) => None,
        }
    }

    /// The caller's stop the lane's refutations poll, if it has one.
    pub(super) fn complete_blast_stop(&self) -> Option<&dyn Fn() -> bool> {
        match self.complete_blast {
            CompleteBlastAsk::AskedUntil(stop) => Some(stop),
            CompleteBlastAsk::Asked | CompleteBlastAsk::NotAsked => None,
        }
    }

    /// Whether the lane's refutations may go on: always, unless the caller's
    /// stop has fired.
    pub(in crate::alethe_printer) fn complete_blast_keeps_going(&self) -> bool {
        self.complete_blast_stop().is_none_or(|stop| !stop())
    }
}
