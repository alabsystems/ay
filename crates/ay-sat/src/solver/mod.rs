// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Solver-origin result wrappers are sealed in `origin_result.rs` and
// re-exported from this module.

//! Main CDCL SAT solver
//!
//! Implements the Conflict-Driven Clause Learning algorithm with:
//! - 2-watched literal scheme for unit propagation
//! - 1UIP conflict analysis with recursive clause minimization
//! - VSIDS (stable mode) and VMTF (focused mode) variable selection
//! - Chronological and non-chronological backtracking (SAT'18 paper)
//! - Lazy reimplication for out-of-order trail literals
//! - Phase saving for decision polarity
//! - Luby and glucose-style EMA restarts
//! - Block-level clause shrinking
//! - DRAT/LRAT proof generation for UNSAT certificates

use crate::bce::{BCEStats, BCE};
use crate::bve::{BVEStats, BVE};
use crate::clause::{ClauseTier, CORE_LBD, TIER1_LBD};
use crate::clause_arena::ClauseArena;
use crate::clause_trace::ClauseTrace;
use crate::condition::Conditioning;
use crate::conflict::{ConflictAnalyzer, ConflictResult};
use crate::congruence::CongruenceClosure;
use crate::decision_trace::{self, DecisionTraceWriter, ReplayTrace, SolveOutcome, TraceEvent};
use crate::decompose::Decompose;
pub use crate::decompose::DecomposeLratPreflightStats;
use crate::diagnostic_trace::{DiagnosticPass, SatDiagnosticWriter};
use crate::extension::{
    ExtCheckResult, ExtContinue, ExtPropagateResult, Extension, PreparedExtension, SolverContext,
};
use crate::factor::Factor;
use crate::gates::GateStats;
use crate::htr::{HTRStats, HTR};
use crate::lit_marks::LitMarks;
use crate::literal::{Literal, Variable};
use crate::mab::{BranchHeuristic, BranchHeuristicStats, BranchSelectorMode, MabController};
use crate::probe::{
    failed_literal_dominator, find_failed_literal_uip, hyper_binary_resolve, ProbeStats, Prober,
};
use crate::proof::ProofOutput;
pub(crate) use crate::proof_certificate::ProofCertificate;
use crate::proof_manager::{ProofAddKind, ProofManager};
use crate::reconstruct::ReconstructionStack;
use crate::subsume::{SubsumeStats, Subsumer};
use crate::sweep::{SweepStats, Sweeper};
use crate::tla_trace::TlaTraceWriter;
use crate::tla_traceable::TlaTraceable;
use crate::transred::TransRed;
use crate::vivify::{VivifyStats, VivifyTier};
use crate::vsids::VSIDS;
use crate::walk::Random;
use crate::watched::{ClauseRef, ExactWatchPlan, WatchList, WatchedLists, Watcher, BINARY_FLAG};
use std::io::Write;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

mod dump;
mod dump_cnf;
pub(crate) mod inproc_engines;
#[cfg(feature = "jit")]
#[allow(dead_code)]
mod jit_compile;
#[cfg(not(feature = "jit"))]
mod jit_stubs;
pub(crate) mod minimization_state;
// Phase-3 live invocation of the external-codegen native install gate (#678).
mod origin_result;
pub(crate) mod phase_init_state;
#[allow(dead_code)]
pub(crate) mod solver_stats;
mod state;
pub(crate) mod tier_state;
mod types;
#[allow(dead_code)]
mod var_data;
pub use dump_cnf::{DumpCnfReport, DumpCnfVerdict, ExtendModelReport};
pub use incremental::VarAssignmentKind;
pub use lookahead::LookaheadStats;
pub use origin_result::{SolverAssumeResult, SolverSatResult};
pub use proof_exhaustion_scope::{
    keep_proof_inprocessing_after_exhaustion, ProofInprocessingKeptAfterExhaustion,
};
pub(crate) use state::ReasonKind;
pub use state::Solver;
pub use stats::{
    BcpLongScanStats, BcpSavedPosStats, IndepEnumReport, LratMaterializationStats,
    RephaseAttributionStats, RestartAttributionStats,
};
#[cfg(test)]
pub(crate) use types::MemoryStats;
pub(crate) use types::WatchOrderPolicy;
pub use types::*;
pub(crate) use types::{LRAT_A, LRAT_B, MIN_KEEP, MIN_POISON, MIN_REMOVABLE, MIN_VISITED};
// SatDebugEnv deleted (#8331) — env-var bridge replaced by global config.
pub(crate) use var_data::{
    binary_reason_lit, is_binary_literal_reason, is_clause_reason, make_binary_reason, VarData,
    NO_REASON,
};

// Solver struct is defined in state.rs (canonical after file split).
// Do NOT add a second `pub struct Solver` here — causes E0255.

// Implement SolverContext for Solver to allow extensions to observe state
impl SolverContext for Solver {
    fn value(&self, var: Variable) -> Option<bool> {
        // A variable above the allocated range is one an extension has
        // MINTED mid-search (see `num_vars`): it is unassigned by
        // definition, and querying it before the solver grows for the
        // returned result must not index the assignment arrays.
        if var.index() >= self.num_vars {
            return None;
        }
        self.var_value_from_vals(var.index())
    }

    fn decision_level(&self) -> u32 {
        self.decision_level
    }

    fn var_level(&self, var: Variable) -> Option<u32> {
        if var.index() >= self.num_vars {
            return None;
        }
        if self.var_is_assigned(var.index()) {
            Some(self.var_data[var.index()].level)
        } else {
            None
        }
    }

    fn trail(&self) -> &[Literal] {
        &self.trail
    }

    fn num_vars(&self) -> usize {
        self.num_vars
    }

    fn conflicts(&self) -> u64 {
        self.num_conflicts
    }

    fn decisions(&self) -> u64 {
        self.num_decisions
    }

    fn restarts(&self) -> u64 {
        self.cold.restarts
    }

    fn propagations(&self) -> u64 {
        self.num_propagations
    }

    fn search_ticks(&self) -> u64 {
        self.total_search_ticks()
    }

    fn activity(&self, var: Variable) -> f64 {
        Self::activity(self, var)
    }

    fn var_reason_side(&self, var: Variable) -> Option<Vec<Literal>> {
        let index = var.index();
        if index >= self.var_data.len() || !self.var_is_assigned(index) {
            return None;
        }
        let data = &self.var_data[index];
        let reason = data.reason;
        if reason == NO_REASON || data.is_lazy_theory_reason() {
            return None;
        }
        if is_binary_literal_reason(reason) {
            return Some(vec![Literal(binary_reason_lit(reason))]);
        }
        // Guard against stale arena offsets exactly like the provenance
        // antecedent walk above (#8490).
        let offset = reason as usize;
        if !self.arena.is_active(offset) {
            return None;
        }
        let side: Vec<Literal> = self
            .arena
            .literals(offset)
            .iter()
            .copied()
            .filter(|lit| lit.variable() != var)
            .collect();
        Some(side)
    }
}

mod arena_gc;
mod assumptions;
mod backtrack;
pub(crate) mod backward_proof;
mod binary_irredundant;
mod branching;
mod build;
mod construction;
mod initial_construct;
pub use initial_construct::CountedInitialSolver;
mod candidate;
pub use candidate::{CandidateSearchOutcome, CandidateSearchWork, CandidateSolver};
mod clause_add;
mod clause_add_internal;
mod clause_id_table;
pub(crate) use clause_id_table::ClauseIdTable;
mod clause_add_theory;
mod clone;
#[allow(dead_code)]
mod cold;
mod cold_restart;
pub(crate) mod compact;
mod compact_fixed;
mod config;
mod config_capability;
mod config_preprocess;
mod config_preprocess_bve;
mod config_preprocess_cleanup;
mod config_preprocess_finalize;
mod config_preprocess_policy;
mod config_preprocess_probe;
mod config_preprocess_symmetry;
mod config_preprocess_transaction;
mod conflict_analysis;
mod conflict_analysis_bumping;
mod conflict_analysis_dip;
mod conflict_analysis_finalize;
mod conflict_analysis_ic3;
mod conflict_analysis_invariants;
mod conflict_analysis_level;
mod conflict_analysis_lrat;
mod conflict_analysis_lrat_specialized;
mod conflict_analysis_lrat_unit_chain;
mod conflict_analysis_minimize;
mod conflict_analysis_minimize_lrat;
#[allow(dead_code)]
mod constants;
mod constrain;
mod consuming_clause_trace;
pub use consuming_clause_trace::{ConsumingTraceControl, ConsumingTraceError, ConsumingTraceStop};
mod counted_admission;
mod decision_admission;
mod decision_commit;
mod det_work;
#[allow(dead_code)]
pub(crate) mod dip;
mod factor_large;
mod factor_marks_undo;
mod flip_to_none;
mod gf_probe;
mod incremental;
mod indep_enum;
mod indep_support;
mod inproc_control;
#[allow(dead_code)]
mod inprocessing;
mod jump_reasons;
pub(crate) mod lifecycle;
mod load_slack;
mod lookahead;
mod lookahead_schedule;
mod lucky_scratch;
mod memory_budget;
mod memory_report;
mod mutate;
mod mutate_delete;
mod mutate_replace;
mod mutate_replace_lrat;
mod mutate_validate;
mod original_clause_ids;
pub(crate) use original_clause_ids::FreshInputTraceEvent;
mod otfs;
mod portfolio_sharing;
mod preprocess;
mod preprocess_kissat;
mod preprocess_reset;
mod preprocess_verify;
mod probe_implications;
#[allow(dead_code)]
mod profile;
mod proof_consumer_lifecycle;
mod proof_emit;
mod proof_exhaustion_scope;
mod propagation;
mod propagation_bcp;
#[cfg(feature = "raw-pointer-bcp")]
#[path = "propagation_bcp_unsafe.rs"]
mod propagation_bcp_unsafe;
mod propagation_dense;
mod random_decision;
pub(crate) mod reap;
mod reduction;
mod reduction_between_solves;
mod reduction_execute;
mod reduction_triggers;
mod reduction_two_stage;
mod relevancy;
mod relevancy_frontier;
mod rephase;
mod restart;
mod sat_whole_loop_guard;
mod shrink;
mod solve;
mod stable_lock;
mod stats;
mod subst_kissat;
mod tracing_config;
mod vars;
mod veripb_define;
mod veripb_derived;
mod veripb_hints;
mod veripb_ready;
mod veripb_stats;
mod veripb_sweep;
mod veripb_units;
mod work_report;
// Experimental (AY_XP_*) probe/vivify/backbone measurement knobs (default-OFF).
pub(crate) mod xp_probe_vivify;

use constants::*;
use tier_state::TIER_RECOMPUTE_INIT;
use xp_probe_vivify::{
    giant_inproc_permille, no_backbone, probe_min_effort, probe_permille, vivify_permille,
};

/// CDCL solver TLA+ trace module and variable constants.
const CDCL_TRACE_MODULE: &str = "cdcl_test";
const CDCL_TRACE_VARIABLES: [&str; 5] = [
    "assignment",
    "trail",
    "state",
    "decisionLevel",
    "learnedClauses",
];
const CDCL_TRACE_ACTIONS: [&str; 6] = [
    "Propagate",
    "DetectConflict",
    "AnalyzeAndLearn",
    "Decide",
    "DeclareSat",
    "DeclareUnsat",
];

#[derive(Clone, Copy)]
enum CdclTraceState {
    Propagating,
    Conflicting,
    Sat,
    Unsat,
}

impl CdclTraceState {
    const fn as_str(self) -> &'static str {
        match self {
            Self::Propagating => "PROPAGATING",
            Self::Conflicting => "CONFLICTING",
            Self::Sat => "SAT",
            Self::Unsat => "UNSAT",
        }
    }
}

#[derive(Clone, Copy)]
enum CdclTraceAction {
    Propagate,
    DetectConflict,
    AnalyzeAndLearn,
    Decide,
    DeclareSat,
    DeclareUnsat,
}

impl CdclTraceAction {
    const fn as_str(self) -> &'static str {
        match self {
            Self::Propagate => CDCL_TRACE_ACTIONS[0],
            Self::DetectConflict => CDCL_TRACE_ACTIONS[1],
            Self::AnalyzeAndLearn => CDCL_TRACE_ACTIONS[2],
            Self::Decide => CDCL_TRACE_ACTIONS[3],
            Self::DeclareSat => CDCL_TRACE_ACTIONS[4],
            Self::DeclareUnsat => CDCL_TRACE_ACTIONS[5],
        }
    }
}

impl TlaTraceable for Solver {
    fn tla_module() -> &'static str {
        CDCL_TRACE_MODULE
    }

    fn tla_variables() -> &'static [&'static str] {
        &CDCL_TRACE_VARIABLES
    }

    fn tla_actions() -> &'static [&'static str] {
        &CDCL_TRACE_ACTIONS
    }

    /// Enable TLA2 trace output for runtime verification.
    ///
    /// When enabled, the solver writes a JSONL trace file at each CDCL action
    /// boundary (propagate, decide, conflict, backtrack, sat, unsat).
    /// The trace file matches TLA2's `TraceHeader`/`TraceStep` format and can
    /// be validated with `TLA2 trace validate`.
    ///
    /// This must be called before `solve()`.
    fn enable_tla_trace(&mut self, path: &str, module: &str, variables: &[&str]) {
        self.cold.tla_trace = Some(TlaTraceWriter::new(path, module, variables));
    }
}

#[allow(clippy::panic)]
#[cfg(test)]
mod tests;
