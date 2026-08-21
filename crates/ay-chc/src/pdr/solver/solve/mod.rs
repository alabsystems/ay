// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Main PDR solve loop and top-level entrypoints.

use super::{
    convergence_monitor::{ConvergenceHealth, StagnationResponse},
    cube, luby, BoundType, CexVerificationResult, ChcExpr, ChcSort, ConvergenceMonitor,
    Counterexample, FxHashMap, GeneralizationStrategy, InitResult, InvariantModel, Lemma,
    PdrResult, PdrSolver, PredicateId, PredicateInterpretation, ProofObligation, ReachFact,
    ReachFactId, SmtResult, StrengthenResult, VerificationProgressSignature, MAX_GLOBAL_LEMMAS,
};

mod fact_summary;
mod main_loop;
mod safety_checks;
mod solve_init;
mod spurious_cex;
#[cfg(test)]
mod tests;
