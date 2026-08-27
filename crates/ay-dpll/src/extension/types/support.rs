// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Auxiliary borrowing modes carried by the eager theory extension.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::TermId;

use crate::executor::BoundRefinementReplayKey;
use crate::proof_tracker::ProofTracker;

pub(in super::super) enum BoundRefinementHandoff<'a> {
    FinalCheckOnly,
    StopAndReplayInline {
        known_replays: &'a HashSet<BoundRefinementReplayKey>,
    },
}

pub(in super::super) struct ProofContext<'a> {
    pub(in super::super) tracker: &'a mut ProofTracker,
    pub(in super::super) negations: &'a HashMap<TermId, TermId>,
}
