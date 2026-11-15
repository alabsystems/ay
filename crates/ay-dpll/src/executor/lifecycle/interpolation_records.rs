// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Proof records for this solver's own Craig interpolation extractor
//! ([`Executor::set_interpolation_proofs`]).

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::{Proof, TermId};

use super::super::Executor;

/// What an interpolation proof session records besides the artifact proof.
#[derive(Default)]
pub(in crate::executor) struct InterpolationRecords {
    /// Host configuration, carried across `(reset)`: this session records the
    /// two per-query fields below.
    pub(in crate::executor) enabled: bool,
    /// Per query: the last UNSAT's refutation as the solver derived it —
    /// preprocessed `assume` leaves, Farkas-annotated lemmas, pruned to the
    /// empty clause's cone — taken before any presentation pass
    /// (`build_unsat_assembly/interpolation.rs`). Read only by the
    /// interpolation extractor; every consumer validates what it serves.
    pub(in crate::executor) last_proof: Option<Proof>,
    /// Per query: for every assertion the last solve handed its SAT/theory
    /// core after preprocessing, the original assertions whose conjunction
    /// implies it (recorded by the QF_LRA lane). The extractor attributes a
    /// preprocessed `assume` leaf to a group only through this record.
    pub(in crate::executor) leaf_sources: Option<HashMap<TermId, Vec<TermId>>>,
}

impl InterpolationRecords {
    /// Forget the last query's records (the session setting stays).
    pub(in crate::executor) fn clear_query(&mut self) {
        self.last_proof = None;
        self.leaf_sources = None;
    }
}

impl Executor {
    /// [`Self::set_best_effort_produce_proofs`], and also record the solver's
    /// own refutation for the Craig interpolation extractor.
    ///
    /// The artifact proof and every verdict are exactly those of best-effort
    /// production. In addition, `build_unsat_proof` keeps the refutation as
    /// the solver derived it, before the presentation passes — which re-spell
    /// `assume` leaves against the parsed surface, demote preprocessed ones to
    /// `trust`, and replace the whole refutation by one `trust` step when the
    /// surface plan or its source-work budget declines, all fatal to
    /// extraction and none of it evidence the extractor can use — and the
    /// QF_LRA lane records which original assertions each preprocessed one
    /// derives from.
    pub fn set_interpolation_proofs(&mut self, step_budget: u64) {
        self.set_best_effort_produce_proofs(step_budget);
        self.interpolation.enabled = true;
    }

    /// The last UNSAT's refutation as the solver derived it, when this
    /// session records one ([`Self::set_interpolation_proofs`]).
    #[must_use]
    pub fn last_interpolation_proof(&self) -> Option<&Proof> {
        if self.last_result_is_unsat() {
            self.interpolation.last_proof.as_ref()
        } else {
            None
        }
    }

    /// The sources of the last solve's preprocessed assertions, when this
    /// session records them ([`InterpolationRecords::leaf_sources`]).
    #[must_use]
    pub(crate) fn interpolation_leaf_sources(&self) -> Option<&HashMap<TermId, Vec<TermId>>> {
        self.interpolation.leaf_sources.as_ref()
    }

    /// Whether proofs are also recorded for the interpolation extractor
    /// ([`Self::set_interpolation_proofs`]).
    #[must_use]
    pub(in crate::executor) fn interpolation_proof(&self) -> bool {
        self.interpolation.enabled
    }
}
