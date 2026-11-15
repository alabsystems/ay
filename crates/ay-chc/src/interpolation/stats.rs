// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! ITP-BOARD: Workstream D interpolation, bridge and engine-exit telemetry.
//!
//! CHC-COMP 2026, the development design notes
//! §4.1 and §10. **Owner: WP-D1-M** (measurement, bridge, ladder).
//!
//! Interface contract **C-M1** (frozen in the day-1 skeleton): [`EngineTag`],
//! [`Source`], [`record_request`], [`record_outcome`],
//! [`record_pre_validation_invalid`], [`record_trust_steps`],
//! [`record_engine_exit`]; line formats `ITP-BOARD: {json}` and
//! `[D-EXIT] engine=<tag> reason=<reason> k=<k>[ <detail>]`.
//!
//! Counters are always recorded (process-global, behind one mutex; every
//! event here is at most once per SMT query, so the lock is not hot). Lines
//! are printed only under the existing `--chc-proof-itp-stats` flag; there is
//! no new user knob. The board line is a cumulative snapshot: it is re-printed
//! on every engine exit and otherwise at most every [`SNAPSHOT_INTERVAL`] while
//! events arrive, so the LAST `ITP-BOARD:` line of a log is the complete
//! record even when the process is killed at its wall-clock limit
//! (consumers should read the last complete record).
//!
//! Telemetry never influences a decision: nothing in the solver reads these
//! counters back.

#![expect(
    dead_code,
    reason = "Workstream D day-1 skeleton: WP-D1-M (board) and WP-D1-P/E (recording) wires these items; remove when used"
)]

use super::proof_groups::{ItpFail, ItpRecipe, ItpUnknown};
use crate::smt::dag_smtlib::DagStats;
use crate::smt::SmtLane;
use ay_core::time::Instant;
use serde_json::{json, Map, Value};
use std::cell::Cell;
use std::collections::BTreeMap;
use std::sync::{Mutex, OnceLock};
use std::time::Duration;

/// Minimum spacing of rate-limited board snapshots.
const SNAPSHOT_INTERVAL: Duration = Duration::from_secs(2);

/// The engine (or caller) on whose behalf an interpolant is requested.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) enum EngineTag {
    Imc,
    Pdkind,
    Kind,
    KTo1,
    Dar,
    Lawi,
    Tpa,
    SplitTpa,
    Pdr,
    Cegar,
    /// A caller that installed no tag (see [`ScopedEngineTag`]).
    Other,
}

impl EngineTag {
    pub(crate) const fn name(self) -> &'static str {
        match self {
            Self::Imc => "imc",
            Self::Pdkind => "pdkind",
            Self::Kind => "kind",
            Self::KTo1 => "k_to_1",
            Self::Dar => "dar",
            Self::Lawi => "lawi",
            Self::Tpa => "tpa",
            Self::SplitTpa => "split_tpa",
            Self::Pdr => "pdr",
            Self::Cegar => "cegar",
            Self::Other => "other",
        }
    }
}

/// Which interpolation source served (or failed) a request.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) enum Source {
    /// Rung 4: same-solve interpolation from Workstream A's session.
    SessionBound,
    /// Rung 1: one proof-producing `ay_dpll::api::Solver` solve per query.
    ProofGroups,
    /// The syntactic cascade (`interpolating_sat_constraints*`).
    Cascade,
}

impl Source {
    pub(crate) const fn name(self) -> &'static str {
        match self {
            Self::SessionBound => "session_bound",
            Self::ProofGroups => "proof_groups",
            Self::Cascade => "cascade",
        }
    }
}

/// How one interpolation request ended.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ItpOutcome {
    /// A (validated, if the source validates) interpolant was served, using
    /// `solves` SMT solves in total (proof solve + Craig checks).
    Served { solves: u32 },
    /// Extraction or validation failed closed.
    Failed(ItpFail),
    /// The source could not decide or did not apply.
    Unknown(ItpUnknown),
}

/// Why an engine loop ended, for `[D-EXIT]` lines.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) enum ExitReason {
    /// A base (reachability) check returned `Unknown`.
    BaseUnknown,
    /// Interpolation failed and the engine could not continue.
    ItpFail,
    /// The engine's own time budget ran out.
    Budget,
    /// The engine reached its unrolling bound.
    MaxK,
    /// The portfolio cancelled the engine.
    Cancelled,
    /// A safe result was produced.
    Safe,
    /// An unsafe result was produced.
    Unsafe,
    /// Anything else (the detail string says what).
    Other,
}

impl ExitReason {
    pub(crate) const fn name(self) -> &'static str {
        match self {
            Self::BaseUnknown => "base_unknown",
            Self::ItpFail => "itp_fail",
            Self::Budget => "budget",
            Self::MaxK => "max_k",
            Self::Cancelled => "cancelled",
            Self::Safe => "safe",
            Self::Unsafe => "unsafe",
            Self::Other => "other",
        }
    }
}

/// How the plain cascade entry obtained its deadline (contract C-M2).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum CascadeDeadline {
    /// The caller passed one (`interpolating_sat_constraints_until`).
    Caller,
    /// The thread's SMT/solve deadline (`effective_thread_deadline`).
    Thread,
    /// No deadline anywhere: `now + 5 s`.
    Default,
}

/// One executor-adapter admission decision (bridge item D-1).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum AdmissionOutcome {
    /// Admitted; sizes of the admitted query.
    Admitted {
        unique_nodes: usize,
        tree_nodes: usize,
    },
    /// Refused: more distinct nodes than the unique-node cap.
    RefusedUniqueNodes,
    /// Refused: nesting deeper than the depth cap.
    RefusedDepth,
    /// Refused: tree expansion larger than the recursive-helper tree cap.
    RefusedTreeSize,
    /// Refused for any other resource or datatype reason.
    RefusedOther,
}

/// How the executor adapter printed one script.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ScriptPrint {
    /// DAG-linear (Search lane).
    Dag { bytes: usize, shared_nodes: usize },
    /// Tree printer (Verification lane, or a DAG-printer refusal).
    Tree { bytes: usize },
    /// The DAG printer refused and the tree printer was used instead.
    DagFallback,
}

// ---------------------------------------------------------------------------
// Engine tag scope (attributes cascade calls to the engine thread)
// ---------------------------------------------------------------------------

thread_local! {
    static CURRENT_ENGINE: Cell<EngineTag> = const { Cell::new(EngineTag::Other) };
}

/// RAII guard naming the engine that runs on this thread, so cascade calls
/// (which take no engine argument; C-M2 forbids a call-site change) are
/// attributed on the board. Engines install it at their entry point.
pub(crate) struct ScopedEngineTag {
    prev: EngineTag,
}

impl ScopedEngineTag {
    pub(crate) fn install(tag: EngineTag) -> Self {
        let prev = CURRENT_ENGINE.with(|cell| cell.replace(tag));
        Self { prev }
    }
}

impl Drop for ScopedEngineTag {
    fn drop(&mut self) {
        let prev = self.prev;
        CURRENT_ENGINE.with(|cell| cell.set(prev));
    }
}

/// The engine tag installed on this thread ([`EngineTag::Other`] if none).
pub(crate) fn current_engine() -> EngineTag {
    CURRENT_ENGINE.with(Cell::get)
}

// ---------------------------------------------------------------------------
// Board state
// ---------------------------------------------------------------------------

/// Log2 histogram of microseconds.
#[derive(Default)]
struct Hist {
    count: u64,
    sum_us: u64,
    max_us: u64,
    buckets: BTreeMap<u32, u64>,
}

impl Hist {
    fn add(&mut self, elapsed: Duration) {
        let us = u64::try_from(elapsed.as_micros()).unwrap_or(u64::MAX);
        self.count += 1;
        self.sum_us = self.sum_us.saturating_add(us);
        self.max_us = self.max_us.max(us);
        let bucket = u64::BITS - us.leading_zeros();
        *self.buckets.entry(bucket).or_default() += 1;
    }

    fn to_json(&self) -> Value {
        let buckets: Vec<Value> = self
            .buckets
            .iter()
            .map(|(bucket, count)| json!([1u64 << bucket.min(&63), count]))
            .collect();
        json!({
            "count": self.count,
            "sum_us": self.sum_us,
            "max_us": self.max_us,
            "le_us": buckets,
        })
    }
}

#[derive(Default)]
struct ItpCell {
    requests: u64,
    served: u64,
    solves: u64,
    pre_validation_invalid: u64,
    trust_steps: u64,
    fail: BTreeMap<&'static str, u64>,
    unknown: BTreeMap<&'static str, u64>,
    elapsed: Hist,
}

#[derive(Default)]
struct StrategyCell {
    tried: u64,
    served: u64,
    craig_invalid: u64,
    no_candidate: u64,
}

#[derive(Default)]
struct CascadeBoard {
    calls: u64,
    deadline_caller: u64,
    deadline_thread: u64,
    deadline_default: u64,
    served: u64,
    unknown: u64,
    by_engine: BTreeMap<&'static str, (u64, u64)>,
    strategies: BTreeMap<&'static str, StrategyCell>,
}

#[derive(Default)]
struct DagAgg {
    count: u64,
    sum_unique: u64,
    max_unique: u64,
    sum_shared: u64,
    max_depth: u64,
}

#[derive(Default)]
struct AdmissionBoard {
    /// (lane, stage, outcome) -> count.
    outcomes: BTreeMap<(&'static str, &'static str, &'static str), u64>,
    max_unique_admitted: u64,
    max_tree_admitted: u64,
}

#[derive(Default)]
struct PrinterBoard {
    dag_scripts: u64,
    dag_bytes: u64,
    dag_shared_nodes: u64,
    tree_scripts: u64,
    tree_bytes: u64,
    dag_fallbacks: u64,
}

#[derive(Default)]
struct Board {
    itp: BTreeMap<(&'static str, &'static str, &'static str), ItpCell>,
    cascade: CascadeBoard,
    proof_solve: Hist,
    extract: Hist,
    dag: DagAgg,
    sat_pair: BTreeMap<&'static str, u64>,
    exits: BTreeMap<(&'static str, &'static str, usize), u64>,
    admission: AdmissionBoard,
    printer: PrinterBoard,
    ladder: BTreeMap<&'static str, u64>,
    last_snapshot: Option<Instant>,
}

fn board() -> &'static Mutex<Board> {
    static BOARD: OnceLock<Mutex<Board>> = OnceLock::new();
    BOARD.get_or_init(|| Mutex::new(Board::default()))
}

fn stats_enabled() -> bool {
    static FLAG: OnceLock<bool> = OnceLock::new();
    *FLAG.get_or_init(|| ay_core::misc_cli_flags().chc_proof_itp_stats)
}

/// Apply `update` to the board, then print a rate-limited snapshot.
fn with_board(update: impl FnOnce(&mut Board)) {
    let snapshot = {
        let Ok(mut guard) = board().lock() else {
            return;
        };
        update(&mut guard);
        take_snapshot_if_due(&mut guard, false)
    };
    if let Some(line) = snapshot {
        safe_eprintln!("{line}");
    }
}

fn take_snapshot_if_due(board: &mut Board, force: bool) -> Option<String> {
    if !stats_enabled() {
        return None;
    }
    let now = Instant::now();
    let due = force
        || board
            .last_snapshot
            .is_none_or(|last| now.saturating_duration_since(last) >= SNAPSHOT_INTERVAL);
    if !due {
        return None;
    }
    board.last_snapshot = Some(now);
    Some(format!("ITP-BOARD: {}", board_to_json(board)))
}

fn recipe_name(recipe: Option<ItpRecipe>) -> &'static str {
    recipe.map_or("none", ItpRecipe::name)
}

fn itp_cell<'b>(
    board: &'b mut Board,
    engine: EngineTag,
    source: Source,
    recipe: Option<ItpRecipe>,
) -> &'b mut ItpCell {
    board
        .itp
        .entry((engine.name(), source.name(), recipe_name(recipe)))
        .or_default()
}

// ---------------------------------------------------------------------------
// C-M1 recording API
// ---------------------------------------------------------------------------

/// One interpolation request reached `source` for `engine`.
pub(crate) fn record_request(engine: EngineTag, source: Source, recipe: Option<ItpRecipe>) {
    with_board(|b| itp_cell(b, engine, source, recipe).requests += 1);
}

/// How a request recorded with [`record_request`] ended.
pub(crate) fn record_outcome(
    engine: EngineTag,
    source: Source,
    recipe: Option<ItpRecipe>,
    outcome: ItpOutcome,
    elapsed: Duration,
) {
    with_board(|b| {
        let cell = itp_cell(b, engine, source, recipe);
        cell.elapsed.add(elapsed);
        match outcome {
            ItpOutcome::Served { solves } => {
                cell.served += 1;
                cell.solves += u64::from(solves);
            }
            ItpOutcome::Failed(fail) => *cell.fail.entry(fail.name()).or_default() += 1,
            ItpOutcome::Unknown(unknown) => *cell.unknown.entry(unknown.name()).or_default() += 1,
        }
    });
}

/// A candidate failed the source's own Craig check before being served
/// (INV-3: counted per source and recipe).
pub(crate) fn record_pre_validation_invalid(
    engine: EngineTag,
    source: Source,
    recipe: Option<ItpRecipe>,
) {
    with_board(|b| itp_cell(b, engine, source, recipe).pre_validation_invalid += 1);
}

/// Trust steps seen in one refutation proof.
pub(crate) fn record_trust_steps(engine: EngineTag, source: Source, steps: usize) {
    with_board(|b| {
        itp_cell(b, engine, source, None).trust_steps += steps as u64;
    });
}

/// Cost and size of one proof-producing solve (`proof_solve_us`,
/// `extract_us`, DAG sizes of its script).
pub(crate) fn record_proof_solve(solve: Duration, extract: Duration, dag: DagStats) {
    with_board(|b| {
        b.proof_solve.add(solve);
        b.extract.add(extract);
        b.dag.count += 1;
        b.dag.sum_unique += dag.unique_nodes as u64;
        b.dag.max_unique = b.dag.max_unique.max(dag.unique_nodes as u64);
        b.dag.sum_shared += dag.shared_nodes as u64;
        b.dag.max_depth = b.dag.max_depth.max(dag.max_depth as u64);
    });
}

/// An interpolation request whose `A ∧ B` turned out satisfiable
/// (`requests_on_sat_pair{caller}`).
pub(crate) fn record_request_on_sat_pair(caller: &'static str) {
    with_board(|b| *b.sat_pair.entry(caller).or_default() += 1);
}

/// An engine loop ended. Prints `[D-EXIT] engine= reason= k=` (under the
/// stats flag) and a board snapshot.
pub(crate) fn record_engine_exit(engine: EngineTag, reason: ExitReason, k: usize) {
    record_engine_exit_detail(engine, reason, k, "");
}

/// [`record_engine_exit`] with free-form `key=value` detail appended to the
/// `[D-EXIT]` line (e.g. `budget_shaped=true`).
pub(crate) fn record_engine_exit_detail(
    engine: EngineTag,
    reason: ExitReason,
    k: usize,
    detail: &str,
) {
    let snapshot = {
        let Ok(mut guard) = board().lock() else {
            return;
        };
        *guard
            .exits
            .entry((engine.name(), reason.name(), k))
            .or_default() += 1;
        take_snapshot_if_due(&mut guard, true)
    };
    if stats_enabled() {
        if detail.is_empty() {
            safe_eprintln!(
                "[D-EXIT] engine={} reason={} k={k}",
                engine.name(),
                reason.name()
            );
        } else {
            safe_eprintln!(
                "[D-EXIT] engine={} reason={} k={k} {detail}",
                engine.name(),
                reason.name()
            );
        }
    }
    if let Some(line) = snapshot {
        safe_eprintln!("{line}");
    }
}

// ---------------------------------------------------------------------------
// WP-D1-M internal recording (cascade, bridge, ladder)
// ---------------------------------------------------------------------------

/// A plain-cascade entry, with the origin of its deadline.
pub(crate) fn record_cascade_call(deadline: CascadeDeadline) {
    let engine = current_engine().name();
    with_board(|b| {
        let cascade = &mut b.cascade;
        cascade.calls += 1;
        match deadline {
            CascadeDeadline::Caller => cascade.deadline_caller += 1,
            CascadeDeadline::Thread => cascade.deadline_thread += 1,
            CascadeDeadline::Default => cascade.deadline_default += 1,
        }
        cascade.by_engine.entry(engine).or_default().0 += 1;
    });
}

/// The cascade's final result for one top-level call.
pub(crate) fn record_cascade_result(served: bool) {
    let engine = current_engine().name();
    with_board(|b| {
        let cascade = &mut b.cascade;
        if served {
            cascade.served += 1;
            cascade.by_engine.entry(engine).or_default().1 += 1;
        } else {
            cascade.unknown += 1;
        }
    });
}

/// How one cascade strategy ended.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum StrategyExit {
    Served,
    CraigInvalid,
    NoCandidate,
}

pub(crate) fn record_cascade_strategy(strategy: &'static str, exit: StrategyExit) {
    with_board(|b| {
        let cell = b.cascade.strategies.entry(strategy).or_default();
        cell.tried += 1;
        match exit {
            StrategyExit::Served => cell.served += 1,
            StrategyExit::CraigInvalid => cell.craig_invalid += 1,
            StrategyExit::NoCandidate => cell.no_candidate += 1,
        }
    });
}

fn lane_name(lane: SmtLane) -> &'static str {
    match lane {
        SmtLane::Search => "search",
        SmtLane::Verification => "verification",
    }
}

/// One executor admission decision (bridge item D-1), by lane and stage
/// (`pre`: the original expression; `post`: after mod/div axiomatization).
pub(crate) fn record_admission(lane: SmtLane, stage: &'static str, outcome: AdmissionOutcome) {
    with_board(|b| {
        let key = match outcome {
            AdmissionOutcome::Admitted {
                unique_nodes,
                tree_nodes,
            } => {
                b.admission.max_unique_admitted =
                    b.admission.max_unique_admitted.max(unique_nodes as u64);
                b.admission.max_tree_admitted =
                    b.admission.max_tree_admitted.max(tree_nodes as u64);
                "admitted"
            }
            AdmissionOutcome::RefusedUniqueNodes => "refused_unique_nodes",
            AdmissionOutcome::RefusedDepth => "refused_depth",
            AdmissionOutcome::RefusedTreeSize => "refused_tree_size",
            AdmissionOutcome::RefusedOther => "refused_other",
        };
        *b.admission
            .outcomes
            .entry((lane_name(lane), stage, key))
            .or_default() += 1;
    });
}

/// How one executor script was printed (bridge item D-1).
pub(crate) fn record_script_print(print: ScriptPrint) {
    with_board(|b| {
        let printer = &mut b.printer;
        match print {
            ScriptPrint::Dag {
                bytes,
                shared_nodes,
            } => {
                printer.dag_scripts += 1;
                printer.dag_bytes += bytes as u64;
                printer.dag_shared_nodes += shared_nodes as u64;
            }
            ScriptPrint::Tree { bytes } => {
                printer.tree_scripts += 1;
                printer.tree_bytes += bytes as u64;
            }
            ScriptPrint::DagFallback => printer.dag_fallbacks += 1,
        }
    });
}

/// A PDR interpolation-ladder event (per-clause disjunction, stage guards).
pub(crate) fn record_ladder(event: &'static str) {
    with_board(|b| *b.ladder.entry(event).or_default() += 1);
}

// ---------------------------------------------------------------------------
// Rendering
// ---------------------------------------------------------------------------

fn counts_json(map: &BTreeMap<&'static str, u64>) -> Value {
    Value::Object(
        map.iter()
            .map(|(k, v)| ((*k).to_owned(), json!(v)))
            .collect::<Map<String, Value>>(),
    )
}

fn board_to_json(b: &Board) -> Value {
    let itp: Vec<Value> = b
        .itp
        .iter()
        .map(|((engine, source, recipe), cell)| {
            json!({
                "engine": engine,
                "source": source,
                "recipe": recipe,
                "requests": cell.requests,
                "served": cell.served,
                "solves": cell.solves,
                "pre_validation_invalid": cell.pre_validation_invalid,
                "trust_steps": cell.trust_steps,
                "fail": counts_json(&cell.fail),
                "unknown": counts_json(&cell.unknown),
                "elapsed": cell.elapsed.to_json(),
            })
        })
        .collect();
    let strategies: Map<String, Value> = b
        .cascade
        .strategies
        .iter()
        .map(|(name, cell)| {
            (
                (*name).to_owned(),
                json!({
                    "tried": cell.tried,
                    "served": cell.served,
                    "craig_invalid": cell.craig_invalid,
                    "no_candidate": cell.no_candidate,
                }),
            )
        })
        .collect();
    let by_engine: Map<String, Value> = b
        .cascade
        .by_engine
        .iter()
        .map(|(engine, (calls, served))| {
            (
                (*engine).to_owned(),
                json!({"calls": calls, "served": served}),
            )
        })
        .collect();
    let exits: Vec<Value> = b
        .exits
        .iter()
        .map(|((engine, reason, k), count)| {
            json!({"engine": engine, "reason": reason, "k": k, "count": count})
        })
        .collect();
    let admission: Map<String, Value> = b
        .admission
        .outcomes
        .iter()
        .map(|((lane, stage, outcome), count)| (format!("{lane}.{stage}.{outcome}"), json!(count)))
        .collect();
    json!({
        "schema": "itp-board-v1",
        "itp": itp,
        "cascade": {
            "calls": b.cascade.calls,
            "calls_without_deadline": b.cascade.calls.saturating_sub(
                b.cascade.deadline_caller + b.cascade.deadline_thread + b.cascade.deadline_default,
            ),
            "deadline_caller": b.cascade.deadline_caller,
            "deadline_thread": b.cascade.deadline_thread,
            "deadline_default_5s": b.cascade.deadline_default,
            "served": b.cascade.served,
            "unknown": b.cascade.unknown,
            "by_engine": by_engine,
            "strategies": strategies,
        },
        "proof_solve_us": b.proof_solve.to_json(),
        "extract_us": b.extract.to_json(),
        "dag": {
            "count": b.dag.count,
            "sum_unique": b.dag.sum_unique,
            "max_unique": b.dag.max_unique,
            "sum_shared": b.dag.sum_shared,
            "max_depth": b.dag.max_depth,
        },
        "requests_on_sat_pair": counts_json(&b.sat_pair),
        "exits": exits,
        "admission": {
            "outcomes": admission,
            "max_unique_admitted": b.admission.max_unique_admitted,
            "max_tree_admitted": b.admission.max_tree_admitted,
        },
        "printer": {
            "dag_scripts": b.printer.dag_scripts,
            "dag_bytes": b.printer.dag_bytes,
            "dag_shared_nodes": b.printer.dag_shared_nodes,
            "tree_scripts": b.printer.tree_scripts,
            "tree_bytes": b.printer.tree_bytes,
            "dag_fallbacks": b.printer.dag_fallbacks,
        },
        "ladder": counts_json(&b.ladder),
    })
}

/// The current board as JSON (tests and the final snapshot).
pub(crate) fn board_json() -> Value {
    board()
        .lock()
        .map_or(Value::Null, |guard| board_to_json(&guard))
}

#[allow(clippy::unwrap_used, clippy::panic)]
#[cfg(test)]
#[path = "stats_tests.rs"]
mod tests;
