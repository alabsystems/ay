// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `--engine=shadow`: the CDCL(T) kernel beside today's lanes, for measurement
//! only (design the development design notes §10.1, M1).
//!
//! At the dispatch seam of a top-level QF_LRA, QF_RDL, QF_IDL, QF_LIA,
//! QF_UF, QF_UFLRA, QF_UFLIA or QF_UFIDL check-sat the executor notes the
//! assertion window the lane was given. When the `(check-sat)` command's
//! verdict is final (after certification and admission), the kernel runs on
//! a clone of the term store, over the same window, with a budget of its
//! own, and one JSON row records both verdicts and the kernel's counters.
//! Only the arithmetic divisions get the LRA lane's preprocessing first (the
//! kernel internalizes `distinct` and term-level `ite` itself).
//!
//! Every top-level check gets a row:
//! - a `(check-sat)` the lane decided without reaching the dispatch seam (an
//!   earlier pass settled it) is shadowed over the assertion stack itself,
//!   with `lane_dispatch` `"not-dispatched"`;
//! - a `(check-sat-assuming ...)` is shadowed over the assertion stack with
//!   its assumptions passed to the kernel as assumptions (`Engine::check`'s
//!   failed-assumption entry), and the model check covers them too.
//!
//! The kernel's answer is never published, and nothing it does reaches the
//! executor: it works on a copy of the store, it runs after the verdict, and
//! the executor's deadlines move forward by the time it took, so a later
//! check-sat's lane keeps its whole budget. The kernel's time across one
//! script is capped at the CLI timeout, which keeps the process inside the
//! watchdog the CLI arms for shadow mode (2T + 3 s).
//!
//! `--engine-shadow-proofs=DIR` (design D3, P1) turns on the kernel's proof
//! recording. The kernel then runs on the AUTHORED assertions rather than the
//! lane's preprocessed window: until preprocessing records its rewrite steps
//! (roadmap item S), only the authored assertions can be the refutation's
//! `assume` leaves. Each `unsat` answer's recorded refutation is assembled,
//! checked by AY's strict checker (every step, no trust) and by the document
//! round-trip check, and written to DIR as an Alethe document for an external
//! checker; the row records the verdicts and the proof's counters.

use std::io::Write;
use std::time::{Duration, Instant};

use ay_cdclt::{
    CheckOutcome, Engine, EngineConfig, EngineStats, Guard, ModelVerdict, ProofFailure, Verdict,
};
use ay_core::{TermId, TermStore};

use super::theories::preprocess_lra;
use super::Executor;
use crate::executor_types::{Result, SolveResult};

mod proof;
use proof::{check_and_write, ProofRequest};

/// The divisions whose check-sats are shadowed. Registration in the kernel is
/// by content; this list only selects what the measurement covers.
const SHADOWED_LOGICS: [&str; 8] = [
    "QF_LRA", "QF_RDL", "QF_IDL", "QF_LIA", "QF_UF", "QF_UFLRA", "QF_UFLIA", "QF_UFIDL",
];

/// Divisions whose window gets the LRA lane's preprocessing first.
const LRA_PREPROCESSED: [&str; 4] = ["QF_LRA", "QF_RDL", "QF_IDL", "QF_LIA"];

/// Kernel budget when the CLI gave no timeout.
const DEFAULT_BUDGET: Duration = Duration::from_secs(10);

/// Shadow bookkeeping carried from the dispatch seam to the verdict.
#[derive(Debug, Default)]
pub(crate) struct EngineShadow {
    /// Nesting depth of `check_sat`; internal probes run at depth > 1 and are
    /// not shadowed.
    depth: u32,
    /// Top-level check-sats shadowed so far (the row's `check` index).
    checks: u64,
    /// Kernel wall time spent so far in this script.
    spent: Duration,
    pending: Option<Pending>,
}

#[derive(Debug)]
struct Pending {
    window: Vec<TermId>,
    /// The `check-sat-assuming` command's assumptions (empty otherwise).
    assumptions: Vec<TermId>,
    command: &'static str,
    logic: &'static str,
    dispatch: &'static str,
    lane_dispatch_seconds: f64,
}

/// What the kernel is given: the formulas, how, and the assumptions.
struct ShadowInput<'a> {
    window: &'a [TermId],
    assumptions: &'a [TermId],
    /// The formulas as given (the authored assertions, or a UF division's
    /// window) rather than under the LRA lane's preprocessing.
    authored: bool,
}

/// What one kernel run produced.
struct KernelRun {
    outcome: CheckOutcome,
    stats: EngineStats,
    plugins: Vec<&'static str>,
    model: Option<ModelVerdict>,
    seconds: f64,
    /// With proof recording: the row's `proof` object.
    proof: Option<serde_json::Value>,
}

/// The `--engine=shadow[:…]` arm's kernel settings.
struct KernelOptions {
    theory_branching: bool,
    difference_logic: bool,
    integer_bcp_implied_bounds: bool,
    /// ay-sat's default search (KC25) instead of the lane-parity profile.
    sat_default: bool,
    /// The relevancy service filters hub propagations (KC21).
    hub_relevancy: bool,
}

fn enabled() -> bool {
    ay_core::misc_cli_flags().engine_shadow
}

/// The shadowed division of the script, if it is one.
fn shadowed_logic(logic: Option<&str>) -> Option<&'static str> {
    logic.and_then(|l| SHADOWED_LOGICS.iter().copied().find(|&s| s == l))
}

fn verdict(result: &Result<SolveResult>) -> &'static str {
    result.as_ref().map_or("error", verdict_of)
}

fn verdict_of(result: &SolveResult) -> &'static str {
    if result.is_sat() {
        "sat"
    } else if result.is_unsat() {
        "unsat"
    } else {
        "unknown"
    }
}

impl Executor {
    /// `check_sat` with the shadow's depth bookkeeping around it.
    pub(in crate::executor) fn check_sat_shadowed(
        &mut self,
        authority: Option<super::AuthoredPlainHardQueryPermit>,
    ) -> Result<SolveResult> {
        self.engine_shadow.depth += 1;
        let result = self.check_sat_with_authority(authority);
        self.engine_shadow.depth = self.engine_shadow.depth.saturating_sub(1);
        result
    }

    /// `check-sat-assuming` with the shadow's bookkeeping around it: the
    /// assertion stack and the assumptions are noted before the solve, and
    /// the solve's own nested checks are not shadowed.
    pub(in crate::executor) fn check_sat_assuming_shadowed(
        &mut self,
        assumptions: &[TermId],
    ) -> Result<SolveResult> {
        if enabled() && self.engine_shadow.depth == 0 {
            if let Some(logic) = shadowed_logic(self.ctx.logic()) {
                self.engine_shadow.pending = Some(Pending {
                    window: self.ctx.assertions.clone(),
                    assumptions: assumptions.to_vec(),
                    command: "check-sat-assuming",
                    logic,
                    dispatch: "none",
                    lane_dispatch_seconds: 0.0,
                });
            }
        }
        self.engine_shadow.depth += 1;
        let result = self.check_sat_assuming_with_named_cores(assumptions);
        self.engine_shadow.depth = self.engine_shadow.depth.saturating_sub(1);
        result
    }

    /// The `(check-sat)` or `(check-sat-assuming ...)` command's verdict is
    /// final: run the kernel on the window noted for it, or on the assertion
    /// stack when the lane never reached the dispatch seam, and record the
    /// row.
    pub(crate) fn engine_shadow_flush(&mut self, published: &SolveResult) {
        let pending = self.engine_shadow.pending.take().or_else(|| {
            let logic = shadowed_logic(self.ctx.logic())?;
            (enabled() && self.engine_shadow.depth == 0).then(|| Pending {
                window: self.ctx.assertions.clone(),
                assumptions: Vec::new(),
                command: "check-sat",
                logic,
                dispatch: "not-dispatched",
                lane_dispatch_seconds: 0.0,
            })
        });
        let Some(pending) = pending else {
            return;
        };
        let started = Instant::now();
        self.engine_shadow_run(pending, published);
        let elapsed = started.elapsed();
        self.engine_shadow.spent += elapsed;
        for cell in [&self.solve_deadline, &self.certification_deadline] {
            if let Some(deadline) = cell.get() {
                cell.set(deadline.checked_add(elapsed).or(Some(deadline)));
            }
        }
    }

    /// The dispatch seam: remember the window the lane was given.
    pub(in crate::executor) fn engine_shadow_note_dispatch(
        &mut self,
        window: &[TermId],
        dispatched: &Result<SolveResult>,
        lane_dispatch_seconds: f64,
    ) {
        if !enabled() || self.engine_shadow.depth != 1 {
            return;
        }
        let Some(logic) = shadowed_logic(self.ctx.logic()) else {
            return;
        };
        self.engine_shadow.pending = Some(Pending {
            window: window.to_vec(),
            assumptions: Vec::new(),
            command: "check-sat",
            logic,
            dispatch: verdict(dispatched),
            lane_dispatch_seconds,
        });
    }

    fn engine_shadow_run(&mut self, pending: Pending, published: &SolveResult) {
        self.engine_shadow.checks += 1;
        let flags = ay_core::misc_cli_flags();
        let budget = self
            .timeout()
            .or_else(|| flags.engine_shadow_budget_ms.map(Duration::from_millis))
            .unwrap_or(DEFAULT_BUDGET)
            .saturating_sub(self.engine_shadow.spent);
        let authored_input = flags.engine_shadow_proofs.is_some() || flags.engine_shadow_authored;
        let authored;
        let window = if authored_input {
            authored = self.proof_original_problem_assertions();
            authored.as_slice()
        } else {
            pending.window.as_slice()
        };
        let request = flags
            .engine_shadow_proofs
            .as_deref()
            .map(|dir| self.engine_shadow_proof_request(dir));
        let input = ShadowInput {
            window,
            assumptions: &pending.assumptions,
            authored: authored_input || !LRA_PREPROCESSED.contains(&pending.logic),
        };
        let run = run_kernel(
            &self.ctx.terms,
            &input,
            budget,
            KernelOptions {
                theory_branching: flags.engine_shadow_theory_branching,
                difference_logic: !flags.engine_shadow_simplex_only,
                integer_bcp_implied_bounds: flags.engine_shadow_lia_bcp_implied,
                sat_default: flags.engine_shadow_sat_default,
                hub_relevancy: flags.engine_shadow_hub_relevancy,
            },
            request,
        );
        let mut row = self.shadow_row(&pending, published, &run, budget, authored_input);
        add_hub_columns(&mut row, &run.stats);
        if let Some(path) = &flags.engine_shadow_log {
            let appended = std::fs::OpenOptions::new()
                .create(true)
                .append(true)
                .open(path)
                .and_then(|mut file| writeln!(file, "{row}"));
            if let Err(error) = appended {
                tracing::warn!(%error, path = %path, "engine shadow: cannot append the row");
            }
        }
    }

    /// One shadow row: both verdicts, the kernel's counters and how it ran.
    fn shadow_row(
        &self,
        pending: &Pending,
        published: &SolveResult,
        run: &KernelRun,
        budget: Duration,
        authored_input: bool,
    ) -> serde_json::Value {
        let flags = ay_core::misc_cli_flags();
        let lane = verdict_of(published);
        let kernel = match run.outcome.verdict {
            Verdict::Sat => "sat",
            Verdict::Unsat => "unsat",
            Verdict::Unknown => "unknown",
        };
        let definite = |v: &str| v == "sat" || v == "unsat";
        serde_json::json!({
            "logic": pending.logic,
            "check": self.engine_shadow.checks,
            "command": pending.command,
            "assumptions": pending.assumptions.len(),
            "lane": lane,
            "lane_dispatch": pending.dispatch,
            "lane_dispatch_seconds": pending.lane_dispatch_seconds,
            "lane_round_trips": self.last_statistics.get_int("dpll.round_trips"),
            "kernel": kernel,
            "kernel_reason": run.outcome.reason.as_deref(),
            "kernel_seconds": run.seconds,
            "kernel_budget_seconds": budget.as_secs_f64(),
            "kernel_theory_branching": flags.engine_shadow_theory_branching,
            "kernel_plugins": run.plugins,
            "kernel_mode": mode_label(flags),
            "kernel_profile": if flags.engine_shadow_sat_default {
                "sat-default"
            } else {
                "lane-parity"
            },
            "kernel_input": if authored_input { "authored" } else { "lane-window" },
            "kernel_recording": flags.engine_shadow_proofs.is_some(),
            "kernel_model": run.model.as_ref().map(model_label),
            "proof": run.proof,
            "disagree": definite(lane) && definite(kernel) && lane != kernel,
            "solve_calls": run.stats.solve_calls,
            "propagate_calls": run.stats.propagate_calls,
            "final_checks": run.stats.final_checks,
            "theory_conflicts": run.stats.conflicts,
            "lemmas": run.stats.lemmas,
            "definitions": run.stats.definitions,
            "minted_atoms": run.stats.minted_atoms,
            "eager_propagations": run.stats.eager_propagations,
            "lazy_propagations": run.stats.lazy_propagations,
            "lazy_explained": run.stats.lazy_explained,
            "sat_conflicts": run.stats.sat_conflicts,
            "sat_decisions": run.stats.sat_decisions,
        })
    }
}

/// The hub's counters (design H1, H3, KC21) as flat row columns.
fn add_hub_columns(row: &mut serde_json::Value, stats: &EngineStats) {
    let columns = serde_json::json!({
        "hub_nodes": stats.hub_nodes,
        "hub_merges": stats.hub_merges,
        "hub_conflicts": stats.hub_conflicts,
        "hub_propagations": stats.hub_propagations,
        "new_eqs": stats.new_eqs,
        "new_diseqs": stats.new_diseqs,
        "combination_equalities": stats.combination_equalities,
        "relevant_marked": stats.relevant_marked,
        "transitivity_lemmas": stats.transitivity_lemmas,
        "resyncs": stats.resyncs,
    });
    if let (Some(row), serde_json::Value::Object(columns)) = (row.as_object_mut(), columns) {
        row.extend(columns);
    }
}

/// Which `--engine=shadow[:…]` arm produced the row.
const fn mode_label(flags: &ay_core::MiscCliFlags) -> &'static str {
    if flags.engine_shadow_hub_relevancy {
        "hub-relevancy"
    } else if flags.engine_shadow_theory_branching {
        "theory-branching"
    } else if flags.engine_shadow_simplex_only {
        "simplex"
    } else if flags.engine_shadow_lia_bcp_implied {
        "lia-bcp-implied"
    } else {
        "default"
    }
}

fn model_label(verdict: &ModelVerdict) -> String {
    match verdict {
        ModelVerdict::Satisfied => "satisfied".to_string(),
        ModelVerdict::Violated(term) => format!("violated:{}", term.0),
        ModelVerdict::Unchecked(why) => format!("unchecked:{why}"),
    }
}

/// One kernel check on a clone of the store, then the exact model check
/// against the checked formulas and the assumptions. The formulas are either
/// the lane's window under the lane's own LRA preprocessing, or (`authored`:
/// the authored assertions, or a UF division's window) the formulas as
/// given; with a proof request the search records its proof.
fn run_kernel(
    terms: &TermStore,
    input: &ShadowInput<'_>,
    budget: Duration,
    options: KernelOptions,
    request: Option<ProofRequest<'_>>,
) -> KernelRun {
    let started = Instant::now();
    let mut store = terms.clone();
    let window = input.window;
    let assertions = if input.authored {
        window.to_vec()
    } else {
        preprocess_lra(&mut store, window.to_vec())
    };
    // The shadow compares the kernel with the lanes, so it searches with the
    // lanes' schedule (KC25's named lane-parity profile) unless the arm asks
    // for the kernel's own.
    let base = if options.sat_default {
        EngineConfig::default()
    } else {
        EngineConfig::lane_parity()
    };
    let mut engine = Engine::new(EngineConfig {
        record_proofs: request.is_some(),
        theory_branching: options.theory_branching,
        difference_logic: options.difference_logic,
        integer_bcp_implied_bounds: options.integer_bcp_implied_bounds,
        hub_relevancy: options.hub_relevancy,
        ..base
    });
    for &assertion in &assertions {
        engine.assert(assertion);
    }
    let guard = Guard::new().with_deadline(started.checked_add(budget));
    let outcome = engine.check(&mut store, input.assumptions, &guard);
    let search_seconds = started.elapsed().as_secs_f64();
    let model = outcome.is_sat().then(|| {
        let checked = [window, input.assumptions].concat();
        engine.check_model(&mut store, &checked)
    });
    let stats = outcome.stats.clone();
    let plugins = engine.plugin_names();
    drop(engine);
    // The proof work (assembly, then the strict check) has a budget of its
    // own, as long as the search's; the CLI watchdog allows for it.
    let proof_deadline = Instant::now().checked_add(budget);
    let assembled = (request.is_some() && outcome.is_unsat()).then(|| {
        let started = Instant::now();
        let proof = outcome
            .proof
            .as_ref()
            .ok_or(ProofFailure::NotRecorded)
            .and_then(|recorded| recorded.assemble(&mut store, proof_deadline));
        (proof, started.elapsed().as_secs_f64())
    });
    let proof = request.map(|request| match assembled {
        None => serde_json::json!({ "status": "no refutation" }),
        Some((Ok(proof), assemble_seconds)) => {
            let mut row = check_and_write(&store, window, &proof, &request, proof_deadline);
            row["assemble_seconds"] = serde_json::json!(assemble_seconds);
            row["search_seconds"] = serde_json::json!(search_seconds);
            row
        }
        Some((Err(failure), assemble_seconds)) => serde_json::json!({
            "status": "not assembled",
            "reason": failure.to_string(),
            "assemble_seconds": assemble_seconds,
        }),
    });
    KernelRun {
        outcome,
        stats,
        plugins,
        model,
        seconds: started.elapsed().as_secs_f64(),
        proof,
    }
}
