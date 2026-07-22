// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Execution mode implementations for the AY CLI.
//!
//! Contains the interactive (stdin), piped, and file-based execution
//! paths. Extracted from `main.rs` to keep each file under 500 lines.

use std::collections::HashMap;
use std::io::{self, BufRead, Read, Write};

use ay_core::escape_string_contents;
use ay_dpll::Executor;
use ay_frontend::{
    parse, sexp::parse_sexp, Command, CommandStream, CommandStreamItem, Constant, FormulaStats,
    IntroKind, SExpr, Sort, Term,
};

use super::firewall_verify::{self, FirewallVerdict};
use super::{
    chc_runner, dimacs, eprintln_smt_error, exit_if_timed_out, explain, explain_reason,
    is_timed_out,
    proof_artifact::{
        write_proof_artifact_or_exit, ProofArtifactProblem, ProofArtifactTheoryMetadata,
    },
    stats_output, ProofConfig, ProofFormat, EXPLAIN_ENABLED, EXPLAIN_FORMAT_JSON,
    GLOBAL_TIMEOUT_MS, INTERRUPT_HANDLE, MINIMIZE_MODEL_ENABLED, PROGRESS_ENABLED,
    PROGRESS_JSON_PATH, SELF_CHECK_ENABLED, START_TIME, STRICT_PROOFS_ENABLED,
    VERIFY_FIREWALL_ENABLED, VERIFY_PROOF_ENABLED, Z3_MODEL_ENABLED, Z3_MODE_ENABLED,
};
use ay::solution_visualization::{render_solution_visualization, VisualizationFormat};

const SMT_FILE_THREAD_STACK_SIZE: usize = 64 * 1024 * 1024;

/// Adapt a proof config for the SMT-LIB execution path.
///
/// When `--verify-proof` auto-defaults on under `cfg(debug_assertions)` (or is
/// explicitly set without a `--proof` override), the synthesizer in
/// `main.rs::build_proof_config` produces a temporary DRAT file because it
/// runs before the input format is known. That config is invalid for SMT-LIB
/// input — SMT solving produces Alethe proofs, not DRAT.
///
/// Rather than reject the run (the pre-existing behavior, documented in
/// the development design notes Finding A — Option A), we rewrite any
/// *synthesized* (`is_temp`) non-Alethe proof config to Alethe with a
/// matching file extension so the default `--verify-proof` behavior is
/// preserved: an Alethe proof is written on UNSAT and the post-solve
/// `verify_proof_file` pipeline skips (rather than errors) on Alethe input.
/// Explicit user-supplied `--proof foo.drat` requests are left untouched so
/// the caller still sees the "SMT-LIB mode requires Alethe" error — that is
/// a real user misconfiguration, not a CLI default glitch.
///
/// Returns `None` when `proof_config` is `None`. Returns `Some(config)`
/// unchanged when no rewrite is needed, and a rewritten owned config
/// otherwise. The caller is expected to use the returned config in place
/// of the input for all downstream handling.
fn adapt_proof_config_for_smt(proof_config: Option<&ProofConfig>) -> Option<ProofConfig> {
    let src = proof_config?;
    // Explicit user requests stay untouched: an incompatible format here
    // indicates a misconfiguration that should surface as an error.
    if !src.is_temp || src.format == ProofFormat::Alethe {
        return Some(src.clone());
    }
    // Synthesized temp proof + non-Alethe format: rewrite for SMT. We also
    // rewrite the extension so the temp file name ends in `.alethe`
    // (the synthesizer produced `ay-verify-<pid>-<nanos>.drat`).
    let new_path = rewrite_extension(&src.path, "alethe");
    Some(ProofConfig {
        path: new_path,
        format: ProofFormat::Alethe,
        binary: false,
        artifact_path: src.artifact_path.clone(),
        is_temp: true,
        synthesized_default: src.synthesized_default,
    })
}

fn logic_from_commands(commands: &[Command]) -> Option<&str> {
    commands.iter().find_map(|command| {
        if let Command::SetLogic(logic) = command {
            Some(logic.as_str())
        } else {
            None
        }
    })
}

/// Replace the extension on `path` with `new_ext` (no leading dot). If the
/// path has no extension, append `.<new_ext>`.
fn rewrite_extension(path: &str, new_ext: &str) -> String {
    let p = std::path::Path::new(path);
    let stem_parent = p
        .parent()
        .map(|parent| {
            if parent.as_os_str().is_empty() {
                String::new()
            } else {
                let mut s = parent.to_string_lossy().to_string();
                s.push(std::path::MAIN_SEPARATOR);
                s
            }
        })
        .unwrap_or_default();
    let stem = p
        .file_stem()
        .map(|s| s.to_string_lossy().to_string())
        .unwrap_or_else(|| path.to_string());
    format!("{stem_parent}{stem}.{new_ext}")
}

/// Remove a synthesized temp proof file after the SMT run completes.
/// No-op when the config is `None`, not marked `is_temp`, or the file is
/// already absent. Used to avoid leaving stray `/tmp/ay-verify-*.alethe`
/// files when `--verify-proof` auto-defaults on under debug builds with
/// no user-supplied `--proof` path (Finding A).
fn cleanup_temp_proof(proof_config: Option<&ProofConfig>) {
    if let Some(proof) = proof_config {
        if proof.is_temp {
            let _ = std::fs::remove_file(&proof.path);
        }
    }
}

/// Create an executor with global timeout interrupt wired in (#2971).
fn new_executor() -> Executor {
    let mut executor = Executor::new();
    if let Some(handle) = INTERRUPT_HANDLE.get() {
        executor.set_interrupt(handle.clone());
    }
    // #8749: Install a wall-clock deadline matching `--timeout` so theory
    // solvers that poll deadlines (IntSat probe, LIA cascade, LRA split loop,
    // …) bail out at the boundary instead of waiting for the watchdog's
    // two-second hard-exit grace period. The watchdog remains the ultimate
    // safety net — this deadline only accelerates cooperative shutdown.
    let ms = GLOBAL_TIMEOUT_MS.load(std::sync::atomic::Ordering::SeqCst);
    if ms > 0 {
        if let Some(start) = START_TIME.get() {
            executor.set_deadline(Some(*start + std::time::Duration::from_millis(ms)));
        }
    }
    // Wire progress flag so SAT solvers inside the SMT pipeline emit
    // periodic status lines when --progress is set.
    if PROGRESS_ENABLED.load(std::sync::atomic::Ordering::Relaxed) {
        executor.set_progress_enabled(true);
    }
    // Wire JSONL progress file path (#8155 subtask 7b).
    if let Some(path) = PROGRESS_JSON_PATH.get() {
        executor.set_progress_json(Some(path.clone()));
    }
    // Wire aggressive model minimization (#8297).
    if MINIMIZE_MODEL_ENABLED.load(std::sync::atomic::Ordering::Relaxed) {
        executor.set_aggressive_model_minimize(true);
    }
    // Strict-proof mode forces internal Alethe proof generation regardless of
    // `--proof` so that the terminal-trust check has a proof to inspect (#8759).
    if strict_proofs_enabled() {
        executor.set_produce_proofs(true);
    }
    // Fail-closed self-check: AY must certify its own answers (model evaluation
    // for SAT, refutation proof for UNSAT) or degrade to a sound `unknown`.
    if self_check_enabled() {
        executor.set_self_check(true);
        // A refutation proof is required to certify UNSAT, so force proof
        // production on even without `--proof`.
        executor.set_produce_proofs(true);
    }
    // Verified-firewall self-cert gate: the firewall Lean is reconstructed from
    // the refutation proof, so proof production must be on even without
    // `--proof`.
    if verify_firewall_enabled() {
        executor.set_produce_proofs(true);
    }
    executor
}

/// Deterministic RUP-replay step budget for the SYNTHESIZED-DEFAULT Alethe
/// certificate (#A2b). SMT-LIB only requires proofs on `:produce-proofs` /
/// `(get-proof)`; the by-default `<input>.alethe` is an ay extra, so it must
/// never trade a fast UNSAT verdict for minutes of proof materialization
/// (QF_UF PEQ: 1s unsat became a 30s-timeout `unknown`). On budget
/// exhaustion the run keeps its verdict and prints the existing
/// "c warning: no proof certificate emitted" degrade. Step count, not wall
/// time, so verdict/artifact behavior is deterministic. Explicit `--proof`,
/// `--strict-proofs`, `--self-check`, and `:produce-proofs` scripts are
/// never budgeted.
const DEFAULT_PROOF_RECONSTRUCTION_STEP_BUDGET: u64 = 1_000_000;

/// Apply the best-effort reconstruction budget for a synthesized-default
/// proof config (never for explicit `--proof`/strict/self-check).
fn apply_default_proof_budget(executor: &mut Executor, proof: &ProofConfig) {
    if proof.synthesized_default && !strict_proofs_enabled() && !self_check_enabled() {
        executor
            .set_proof_reconstruction_step_budget(Some(DEFAULT_PROOF_RECONSTRUCTION_STEP_BUDGET));
    }
}

/// `true` when `--self-check` was set.
fn self_check_enabled() -> bool {
    SELF_CHECK_ENABLED.load(std::sync::atomic::Ordering::Relaxed)
}

/// `true` when `--strict-proofs` was set.
fn strict_proofs_enabled() -> bool {
    STRICT_PROOFS_ENABLED.load(std::sync::atomic::Ordering::Relaxed)
}

/// `true` when `--verify-firewall` was set.
fn verify_firewall_enabled() -> bool {
    VERIFY_FIREWALL_ENABLED.load(std::sync::atomic::Ordering::Relaxed)
}

/// Whether the assertion set seen by `check-sat` is the COMPLETE problem.
///
/// A command that contributes to the problem (an `assert`, a declaration, a
/// definition, a stack op, ...) but fails to parse or elaborate is reported as a
/// recoverable `(error ...)` and then DROPPED. Dropping a constraint can only
/// turn UNSAT into SAT, so once any such command is discarded the solver must
/// fail closed: a subsequent `check-sat` answers `unknown`, never a definitive
/// sat/unsat on the incomplete remainder. (#match-soundness, Part 1.)
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
enum ProblemCompleteness {
    /// Every problem-contributing command so far was processed in full.
    #[default]
    Complete,
    /// At least one problem-contributing command was discarded.
    Incomplete,
}

#[derive(Default)]
struct SmtTranscriptState {
    print_success: bool,
    interactive_mode: bool,
    produce_assignments: bool,
    produce_proofs: bool,
    produce_unsat_assumptions: bool,
    global_decls: bool,
    auto_config: bool,
    model_v2: bool,
    model_compact: bool,
    pp_decimal: bool,
    pp_decimal_precision: String,
    pp_max_depth: String,
    pp_max_ribbon: String,
    pp_single_line: bool,
    pp_bv_literals: bool,
    regular_output_channel: String,
    diagnostic_output_channel: String,
    verbosity: String,
    rlimit_option: String,
    z3_compat_bool_options: HashMap<String, bool>,
    status: Option<String>,
    rlimit: u64,
    assertion_stack_depth: u32,
    executor_assertion_stack_depth: u32,
    symbol_sorts: HashMap<String, String>,
    current_source: Option<CommandSource>,
    current_command_ordinal: usize,
    processed_commands: usize,
    had_recoverable_error: bool,
    recoverable_error_count: usize,
    completeness: ProblemCompleteness,
}

#[derive(Clone, Debug)]
struct CommandSource {
    line: usize,
    column: usize,
    text: String,
}

#[derive(Clone, Copy, Debug)]
struct SourcePosition {
    line: usize,
    column: usize,
}

impl SmtTranscriptState {
    fn new() -> Self {
        Self {
            print_success: false,
            interactive_mode: false,
            produce_assignments: false,
            produce_proofs: false,
            produce_unsat_assumptions: false,
            global_decls: false,
            auto_config: true,
            model_v2: false,
            model_compact: true,
            pp_decimal: false,
            pp_decimal_precision: "10".to_string(),
            pp_max_depth: "5".to_string(),
            pp_max_ribbon: "80".to_string(),
            pp_single_line: false,
            pp_bv_literals: true,
            regular_output_channel: "stdout".to_string(),
            diagnostic_output_channel: "stderr".to_string(),
            verbosity: "0".to_string(),
            rlimit_option: "0".to_string(),
            z3_compat_bool_options: z3_compat_bool_option_defaults(),
            status: Some("unknown".to_string()),
            rlimit: 1,
            assertion_stack_depth: 0,
            executor_assertion_stack_depth: 0,
            symbol_sorts: HashMap::new(),
            current_source: None,
            current_command_ordinal: 0,
            processed_commands: 0,
            had_recoverable_error: false,
            recoverable_error_count: 0,
            completeness: ProblemCompleteness::Complete,
        }
    }

    fn note_recoverable_error(&mut self) {
        self.had_recoverable_error = true;
        self.recoverable_error_count = self.recoverable_error_count.saturating_add(1);
    }

    /// Mark the problem as incomplete: a problem-contributing command was
    /// dropped, so a later `check-sat` must answer `unknown` (fail closed).
    fn mark_incomplete(&mut self) {
        self.completeness = ProblemCompleteness::Incomplete;
    }

    fn is_incomplete(&self) -> bool {
        self.completeness == ProblemCompleteness::Incomplete
    }
}

/// True when a top-level command that just FAILED TO PARSE (and was therefore
/// dropped) contributes to the satisfiability problem, so the session must be
/// tainted to `unknown`. `consumed` is the exact source slice the command stream
/// read for the failed item — for a cleanly-parsed-but-invalid command (e.g. an
/// `assert` whose body uses an unsupported construct) this is precisely that
/// command's text, so its leading keyword is a reliable signal. A malformed
/// S-expression (e.g. a stray `)`) does not start with `(<keyword>` and is left
/// untainted, preserving z3-style continued-execution for such structural slips.
fn parse_drop_contributes_to_problem(consumed: &str) -> bool {
    command_source_keyword(consumed).is_some_and(command_keyword_contributes_to_problem)
}

fn invalidate_export_after_malformed_decision(source: &str) {
    if ay_core::trace_config().dump_bv_cnf_path.is_none()
        || !command_source_keyword(source)
            .is_some_and(|keyword| matches!(keyword, "check-sat" | "check-sat-assuming"))
    {
        return;
    }
    if let Err(error) = Executor::invalidate_bv_cnf_export_for_rejected_check() {
        eprintln_smt_error(error.to_string());
    }
}

/// Extract the leading command keyword from a top-level command's raw source
/// text (a balanced `(...)` chunk). Returns the symbol immediately after the
/// opening paren, or `None` when the text is not a simple `(<keyword> ...)`.
fn command_source_keyword(text: &str) -> Option<&str> {
    let body = text.trim_start().strip_prefix('(')?.trim_start();
    let end = body
        .find(|c: char| c.is_whitespace() || c == '(' || c == ')')
        .unwrap_or(body.len());
    let keyword = &body[..end];
    (!keyword.is_empty()).then_some(keyword)
}

/// Command keywords whose failure to parse changes the satisfiability of the
/// problem: anything that asserts a constraint, declares/defines a symbol or
/// sort, or manipulates the assertion stack. Pure queries and options
/// (`get-*`, `set-*`, `echo`, ...) are deliberately excluded — discarding one
/// cannot flip a sat/unsat verdict, so the solver stays answerable (matching
/// z3's continued-execution).
fn command_keyword_contributes_to_problem(keyword: &str) -> bool {
    matches!(
        keyword,
        "assert"
            | "assert-soft"
            | "minimize"
            | "maximize"
            | "declare-const"
            | "declare-fun"
            | "declare-sort"
            | "define-sort"
            | "declare-datatype"
            | "declare-datatypes"
            | "define-fun"
            | "define-fun-rec"
            | "define-funs-rec"
            | "declare-rel"
            | "declare-var"
            | "rule"
            | "query"
            | "push"
            | "pop"
            | "reset"
            | "reset-assertions"
            // z3's `(include "file")` extension splices the file's commands
            // inline. AY does not implement it, so it fails to parse ("Unknown
            // command: include") and is DROPPED — silently discarding every
            // assertion/declaration the included file contributes. Treating it
            // as problem-contributing taints the session so a later check-sat
            // fails closed to `unknown` instead of answering `sat` on the
            // (constraint-stripped) remainder — a confirmed wrong-`sat` class
            // when the included file is unsatisfiable. (burndown item #3)
            | "include"
    )
}

/// Parsed-command analogue of [`command_keyword_contributes_to_problem`]: true
/// when discarding `cmd` after an ELABORATION failure could change a sat/unsat
/// verdict, so the session must be tainted to `unknown`.
fn command_contributes_to_problem(cmd: &Command) -> bool {
    matches!(
        cmd,
        Command::Assert(_)
            | Command::AssertSoft { .. }
            | Command::Maximize(_)
            | Command::Minimize(_)
            | Command::DeclareConst(..)
            | Command::DeclareFun(..)
            | Command::DeclareSort(..)
            | Command::DefineSort(..)
            | Command::DeclareDatatype(..)
            | Command::DeclareDatatypes(..)
            | Command::DefineFun(..)
            | Command::DefineFunRec(..)
            | Command::DefineFunsRec(..)
            | Command::Push(_)
            | Command::Pop(_)
    )
}

fn collect_command_sources(input: &str) -> Vec<CommandSource> {
    collect_command_sources_from_line(input, 1)
}

/// Like [`collect_command_sources`] but numbers the first line `line_base`
/// instead of 1. The streaming `-in` path parses one command chunk at a time and
/// clears the buffer between chunks, so it threads a running line count here to
/// keep error positions cumulative across the whole session — z3 reports the
/// true whole-input line number in `-in` mode, not a per-command reset.
fn collect_command_sources_from_line(input: &str, line_base: usize) -> Vec<CommandSource> {
    let mut sources = Vec::new();
    let mut line = line_base;
    let mut column = 1usize;
    let mut depth = 0usize;
    let mut start_idx = 0usize;
    let mut start_line = line_base;
    let mut start_column = 1usize;
    let mut in_comment = false;
    let mut in_string = false;
    let mut chars = input.char_indices().peekable();

    while let Some((idx, ch)) = chars.next() {
        if in_comment {
            if ch == '\n' {
                in_comment = false;
                line += 1;
                column = 1;
            } else {
                column += 1;
            }
            continue;
        }

        if in_string {
            if ch == '"' {
                if let Some((_, '"')) = chars.peek().copied() {
                    let _ = chars.next();
                    column += 2;
                    continue;
                }
                in_string = false;
            }
            if ch == '\n' {
                line += 1;
                column = 1;
            } else {
                column += 1;
            }
            continue;
        }

        match ch {
            ';' => in_comment = true,
            '"' => in_string = true,
            '(' => {
                if depth == 0 {
                    start_idx = idx;
                    start_line = line;
                    start_column = column;
                }
                depth = depth.saturating_add(1);
            }
            ')' if depth > 0 => {
                depth -= 1;
                if depth == 0 {
                    let end = idx + ch.len_utf8();
                    sources.push(CommandSource {
                        line: start_line,
                        column: start_column,
                        text: input[start_idx..end].to_string(),
                    });
                }
            }
            _ => {}
        }

        if ch == '\n' {
            line += 1;
            column = 1;
        } else {
            column += 1;
        }
    }

    sources
}

fn set_current_command_source(
    state: &mut SmtTranscriptState,
    sources: &[CommandSource],
    index: usize,
) {
    state.current_source = sources.get(index).cloned();
    state.current_command_ordinal = state.processed_commands;
    state.processed_commands = state.processed_commands.saturating_add(1);
}

fn source_position_at(source: &CommandSource, byte_offset: usize) -> SourcePosition {
    let mut line = source.line;
    let mut column = source.column;
    let capped_offset = byte_offset.min(source.text.len());

    for (_, ch) in source
        .text
        .char_indices()
        .take_while(|(idx, _)| *idx < capped_offset)
    {
        if ch == '\n' {
            line += 1;
            column = 1;
        } else {
            column += 1;
        }
    }

    SourcePosition { line, column }
}

fn source_error(position: Option<SourcePosition>, message: &str) -> String {
    let message = if let Some(position) = position {
        format!(
            "line {} column {}: {message}",
            position.line, position.column
        )
    } else {
        message.to_string()
    };
    format!("(error \"{}\")", escape_string_contents(&message))
}

fn z3_parser_symbol_position(
    state: &SmtTranscriptState,
    mut position: SourcePosition,
) -> SourcePosition {
    if state.current_command_ordinal > 0 {
        position.column = position.column.saturating_sub(1);
    }
    position
}

fn z3_parser_application_position(
    state: &SmtTranscriptState,
    mut position: SourcePosition,
) -> SourcePosition {
    if state.current_command_ordinal == 0 {
        position.column = position.column.saturating_add(1);
    }
    position
}

fn write_transcript_line(channel: &str, line: &str) {
    match channel {
        "stdout" => safe_println!("{line}"),
        "stderr" => safe_eprintln!("{line}"),
        path => match std::fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open(path)
        {
            Ok(mut file) => {
                let _ = writeln!(file, "{line}");
            }
            Err(err) => {
                safe_eprintln!("warning: failed to write SMT-LIB transcript channel {path}: {err}");
            }
        },
    }
}

fn prepare_transcript_channel(channel: &str) {
    if matches!(channel, "stdout" | "stderr") {
        return;
    }
    if let Err(err) = std::fs::File::create(channel) {
        safe_eprintln!("warning: failed to open SMT-LIB transcript channel {channel}: {err}");
    }
}

fn print_regular_line(state: &SmtTranscriptState, line: &str) {
    write_transcript_line(&state.regular_output_channel, line);
}

fn print_diagnostic_line(state: &SmtTranscriptState, line: &str) {
    write_transcript_line(&state.diagnostic_output_channel, line);
}

fn z3_unsupported_query_position(state: &SmtTranscriptState) -> Option<SourcePosition> {
    let source = state.current_source.as_ref()?;
    let column = if state.current_command_ordinal == 0 {
        source.column
    } else {
        source.column.saturating_sub(1)
    };
    Some(SourcePosition {
        line: source.line,
        column,
    })
}

fn z3_unsupported_query_comment(state: &SmtTranscriptState, keyword: &str) -> String {
    if let Some(position) = z3_unsupported_query_position(state) {
        format!(
            "; {} line: {} position: {}",
            keyword_with_colon(keyword),
            position.line,
            position.column
        )
    } else {
        format!("; {} unsupported", keyword_with_colon(keyword))
    }
}

fn eprintln_z3_unsupported_query_comment(state: &SmtTranscriptState, keyword: &str) {
    print_diagnostic_line(state, &z3_unsupported_query_comment(state, keyword));
}

fn current_source_last_token_position(state: &SmtTranscriptState) -> Option<SourcePosition> {
    let source = state.current_source.as_ref()?;
    let close_idx = source.text.rfind(')')?;
    let token_idx = source.text[..close_idx]
        .char_indices()
        .rev()
        .find_map(|(idx, ch)| (!ch.is_whitespace()).then_some(idx))?;
    Some(source_position_at(source, token_idx))
}

fn invalid_status_position(state: &SmtTranscriptState) -> Option<SourcePosition> {
    let source = state.current_source.as_ref()?;
    let status_idx = source.text.find(":status")?;
    Some(source_position_at(source, status_idx + ":status".len()))
}

fn keyword_key(keyword: &str) -> &str {
    keyword.trim_start_matches(':')
}

fn is_global_decls_option(key: &str) -> bool {
    matches!(key, "global-declarations" | "global-decls")
}

fn keyword_with_colon(keyword: &str) -> String {
    if keyword.starts_with(':') {
        keyword.to_string()
    } else {
        format!(":{keyword}")
    }
}

fn sexpr_bool(value: &SExpr) -> Option<bool> {
    match value {
        SExpr::True => Some(true),
        SExpr::False => Some(false),
        SExpr::Symbol(symbol) if symbol == "true" => Some(true),
        SExpr::Symbol(symbol) if symbol == "false" => Some(false),
        _ => None,
    }
}

fn sexpr_string(value: &SExpr) -> Option<&str> {
    match value {
        SExpr::String(value) => Some(value),
        _ => None,
    }
}

fn sexpr_numeral(value: &SExpr) -> Option<&str> {
    match value {
        SExpr::Numeral(value) => Some(value),
        _ => None,
    }
}

fn sexpr_status(value: &SExpr) -> Option<&'static str> {
    match value {
        SExpr::Symbol(symbol) if symbol == "sat" => Some("sat"),
        SExpr::Symbol(symbol) if symbol == "unsat" => Some("unsat"),
        SExpr::Symbol(symbol) if symbol == "unknown" => Some("unknown"),
        _ => None,
    }
}

fn is_invalid_status_attribute(cmd: &Command) -> bool {
    matches!(
        cmd,
        Command::SetInfo(keyword, SExpr::Symbol(_))
            if keyword_key(keyword) == "status" && sexpr_status_value(cmd).is_none()
    )
}

fn sexpr_status_value(cmd: &Command) -> Option<&'static str> {
    let Command::SetInfo(_, value) = cmd else {
        return None;
    };
    sexpr_status(value)
}

fn maybe_handle_cli_transcript_command(state: &mut SmtTranscriptState, cmd: &Command) -> bool {
    if matches!(cmd, Command::GetUnsatAssumptions) && !state.produce_unsat_assumptions {
        print_regular_line(
            state,
            &source_error(
                current_source_last_token_position(state),
                "unsat assumptions construction is not enabled, use command (set-option :produce-unsat-assumptions true)",
            ),
        );
        state.note_recoverable_error();
        return true;
    }

    if matches!(cmd, Command::GetProof) && !state.produce_proofs {
        print_regular_line(
            state,
            &source_error(
                current_source_last_token_position(state),
                "proof construction is not enabled, use command (set-option :produce-proofs true)",
            ),
        );
        state.note_recoverable_error();
        return true;
    }

    if matches!(cmd, Command::GetAssertions) && !state.interactive_mode {
        print_regular_line(
            state,
            &source_error(
                current_source_last_token_position(state),
                "command is only available in interactive mode, use command (set-option :interactive-mode true)",
            ),
        );
        state.note_recoverable_error();
        return true;
    }

    if let Command::Pop(depth) = cmd {
        if *depth > state.assertion_stack_depth {
            print_regular_line(
                state,
                &source_error(
                    current_source_last_token_position(state),
                    "invalid pop command, argument is greater than the current stack depth",
                ),
            );
            state.note_recoverable_error();
            return true;
        }

        if *depth > state.executor_assertion_stack_depth {
            update_transcript_state_after_command(state, cmd);
            maybe_print_success(state);
            return true;
        }
    }

    if is_invalid_status_attribute(cmd) {
        print_regular_line(
            state,
            &source_error(
                invalid_status_position(state),
                "invalid ':status' attribute",
            ),
        );
        state.note_recoverable_error();
        return true;
    }

    if let Command::SetOption(keyword, value) = cmd {
        let key = keyword_key(keyword);
        if key == "auto-config" && sexpr_bool(value).is_some() {
            update_transcript_state_after_command(state, cmd);
            maybe_print_success(state);
            return true;
        }
        if key == "model.v2" && sexpr_bool(value).is_some() {
            update_transcript_state_after_command(state, cmd);
            maybe_print_success(state);
            return true;
        }
        if key == "model.compact" && sexpr_bool(value).is_some() {
            update_transcript_state_after_command(state, cmd);
            maybe_print_success(state);
            return true;
        }
        if key == "pp.decimal" && sexpr_bool(value).is_some() {
            update_transcript_state_after_command(state, cmd);
            maybe_print_success(state);
            return true;
        }
        if key == "pp.decimal-precision" && sexpr_numeral(value).is_some() {
            update_transcript_state_after_command(state, cmd);
            maybe_print_success(state);
            return true;
        }
        if key == "pp.max-depth" && sexpr_numeral(value).is_some() {
            update_transcript_state_after_command(state, cmd);
            maybe_print_success(state);
            return true;
        }
        if key == "pp.max-ribbon" && sexpr_numeral(value).is_some() {
            update_transcript_state_after_command(state, cmd);
            maybe_print_success(state);
            return true;
        }
        if key == "pp.single-line" && sexpr_bool(value).is_some() {
            update_transcript_state_after_command(state, cmd);
            maybe_print_success(state);
            return true;
        }
        if key == "pp.bv-literals" && sexpr_bool(value).is_some() {
            update_transcript_state_after_command(state, cmd);
            maybe_print_success(state);
            return true;
        }
        if matches!(key, "regular-output-channel" | "diagnostic-output-channel")
            && sexpr_string(value).is_some()
        {
            update_transcript_state_after_command(state, cmd);
            maybe_print_success(state);
            return true;
        }
        if key == "verbosity" && sexpr_numeral(value).is_some() {
            update_transcript_state_after_command(state, cmd);
            maybe_print_success(state);
            return true;
        }
        if key == "rlimit" && sexpr_numeral(value).is_some() {
            update_transcript_state_after_command(state, cmd);
            maybe_print_success(state);
            return true;
        }
        if is_z3_compat_bool_option(key) && sexpr_bool(value).is_some() {
            update_transcript_state_after_command(state, cmd);
            maybe_print_success(state);
            return true;
        }
    }
    false
}

fn sort_text(sort: &Sort) -> String {
    match sort {
        Sort::Simple(name) => name.clone(),
        Sort::Parameterized(name, args) => {
            let mut parts = Vec::with_capacity(args.len() + 1);
            parts.push(name.clone());
            parts.extend(args.iter().map(sort_text));
            format!("({})", parts.join(" "))
        }
        Sort::Indexed(name, indices) => {
            let mut parts = Vec::with_capacity(indices.len() + 2);
            parts.push("_".to_string());
            parts.push(name.clone());
            parts.extend(indices.iter().cloned());
            format!("({})", parts.join(" "))
        }
        _ => "Unknown".to_string(),
    }
}

fn constant_sort_text(value: &Constant) -> String {
    match value {
        Constant::True | Constant::False => "Bool".to_string(),
        Constant::Numeral(_) => "Int".to_string(),
        Constant::Decimal(_) => "Real".to_string(),
        Constant::Hexadecimal(bits) => format!("(_ BitVec {})", bits.len() * 4),
        Constant::Binary(bits) => format!("(_ BitVec {})", bits.len()),
        Constant::String(_) => "String".to_string(),
        _ => "Unknown".to_string(),
    }
}

fn parse_sort_text(text: &str) -> Option<Sort> {
    let sexp = parse_sexp(text).ok()?;
    Sort::from_sexp(&sexp).ok()
}

fn array_sort_parts(sort: &str) -> Option<(String, String)> {
    let Sort::Parameterized(name, args) = parse_sort_text(sort)? else {
        return None;
    };
    if name != "Array" || args.len() != 2 {
        return None;
    }
    Some((sort_text(&args[0]), sort_text(&args[1])))
}

fn infer_numeric_sort_text(
    state: &SmtTranscriptState,
    locals: &HashMap<String, Option<String>>,
    args: &[Term],
) -> Option<String> {
    let mut saw_real = false;
    for arg in args {
        match infer_term_sort_text_with_locals(state, locals, arg)?.as_str() {
            "Int" => {}
            "Real" => saw_real = true,
            _ => return None,
        }
    }
    Some(if saw_real { "Real" } else { "Int" }.to_string())
}

fn all_args_have_sort(
    state: &SmtTranscriptState,
    locals: &HashMap<String, Option<String>>,
    args: &[Term],
    expected: &str,
) -> Option<()> {
    args.iter()
        .all(|arg| {
            infer_term_sort_text_with_locals(state, locals, arg).as_deref() == Some(expected)
        })
        .then_some(())
}

fn infer_app_sort_text(
    state: &SmtTranscriptState,
    locals: &HashMap<String, Option<String>>,
    name: &str,
    args: &[Term],
) -> Option<String> {
    match name {
        "+" | "-" | "*" | "/" if !args.is_empty() => infer_numeric_sort_text(state, locals, args),
        "div" | "mod" | "abs" if !args.is_empty() => {
            all_args_have_sort(state, locals, args, "Int")?;
            Some("Int".to_string())
        }
        "<" | "<=" | ">" | ">=" if !args.is_empty() => {
            infer_numeric_sort_text(state, locals, args)?;
            Some("Bool".to_string())
        }
        "=" | "distinct" if !args.is_empty() => args
            .iter()
            .all(|arg| infer_term_sort_text_with_locals(state, locals, arg).is_some())
            .then_some("Bool".to_string()),
        "and" | "or" | "xor" | "=>" if !args.is_empty() => {
            all_args_have_sort(state, locals, args, "Bool")?;
            Some("Bool".to_string())
        }
        "not" if args.len() == 1 => {
            all_args_have_sort(state, locals, args, "Bool")?;
            Some("Bool".to_string())
        }
        "ite" if args.len() == 3 => {
            (infer_term_sort_text_with_locals(state, locals, &args[0]).as_deref() == Some("Bool"))
                .then_some(())?;
            let then_sort = infer_term_sort_text_with_locals(state, locals, &args[1])?;
            (infer_term_sort_text_with_locals(state, locals, &args[2]).as_deref()
                == Some(then_sort.as_str()))
            .then_some(then_sort)
        }
        "to_real" if args.len() == 1 => {
            all_args_have_sort(state, locals, args, "Int")?;
            Some("Real".to_string())
        }
        "to_int" if args.len() == 1 => {
            all_args_have_sort(state, locals, args, "Real")?;
            Some("Int".to_string())
        }
        "is_int" if args.len() == 1 => {
            all_args_have_sort(state, locals, args, "Real")?;
            Some("Bool".to_string())
        }
        "select" if args.len() == 2 => {
            let array_sort = infer_term_sort_text_with_locals(state, locals, &args[0])?;
            let (index_sort, element_sort) = array_sort_parts(&array_sort)?;
            (infer_term_sort_text_with_locals(state, locals, &args[1]).as_deref()
                == Some(index_sort.as_str()))
            .then_some(element_sort)
        }
        "store" if args.len() == 3 => {
            let array_sort = infer_term_sort_text_with_locals(state, locals, &args[0])?;
            let (index_sort, element_sort) = array_sort_parts(&array_sort)?;
            (infer_term_sort_text_with_locals(state, locals, &args[1]).as_deref()
                == Some(index_sort.as_str()))
            .then_some(())?;
            (infer_term_sort_text_with_locals(state, locals, &args[2]).as_deref()
                == Some(element_sort.as_str()))
            .then_some(array_sort)
        }
        _ => None,
    }
}

fn infer_term_sort_text_with_locals(
    state: &SmtTranscriptState,
    locals: &HashMap<String, Option<String>>,
    term: &Term,
) -> Option<String> {
    match term {
        Term::Const(value) => Some(constant_sort_text(value)),
        Term::Symbol(symbol) => {
            if let Some(local_sort) = locals.get(symbol) {
                return local_sort.clone();
            }
            state.symbol_sorts.get(symbol).cloned()
        }
        Term::App(name, args) => infer_app_sort_text(state, locals, name, args),
        Term::IndexedApp(name, _, args) => infer_app_sort_text(state, locals, name, args),
        Term::Let(bindings, body) => {
            let mut extended = locals.clone();
            for (name, binding) in bindings {
                extended.insert(
                    name.clone(),
                    infer_term_sort_text_with_locals(state, locals, binding),
                );
            }
            infer_term_sort_text_with_locals(state, &extended, body)
        }
        Term::Annotated(inner, _) => infer_term_sort_text_with_locals(state, locals, inner),
        Term::QualifiedApp(_, sort, _) => Some(sort_text(sort)),
        _ => None,
    }
}

fn extend_sorted_sort_locals(
    locals: &HashMap<String, Option<String>>,
    bindings: &[(String, Sort)],
) -> HashMap<String, Option<String>> {
    let mut extended = locals.clone();
    for (name, sort) in bindings {
        extended.insert(name.clone(), Some(sort_text(sort)));
    }
    extended
}

fn extend_let_sort_locals(
    state: &SmtTranscriptState,
    locals: &HashMap<String, Option<String>>,
    bindings: &[(String, Term)],
) -> HashMap<String, Option<String>> {
    let mut extended = locals.clone();
    for (name, binding) in bindings {
        extended.insert(
            name.clone(),
            infer_term_sort_text_with_locals(state, locals, binding),
        );
    }
    extended
}

fn find_application_arg_sorts(
    state: &SmtTranscriptState,
    term: &Term,
    symbol: &str,
) -> Option<Vec<String>> {
    let locals = HashMap::new();
    find_application_arg_sorts_with_locals(state, &locals, term, symbol)
}

fn find_application_arg_sorts_with_locals(
    state: &SmtTranscriptState,
    locals: &HashMap<String, Option<String>>,
    term: &Term,
    symbol: &str,
) -> Option<Vec<String>> {
    match term {
        Term::App(name, args) | Term::IndexedApp(name, _, args) if name == symbol => args
            .iter()
            .map(|arg| infer_term_sort_text_with_locals(state, locals, arg))
            .collect(),
        Term::QualifiedApp(name, _, args) if name == symbol => args
            .iter()
            .map(|arg| infer_term_sort_text_with_locals(state, locals, arg))
            .collect(),
        Term::App(_, args) | Term::IndexedApp(_, _, args) | Term::QualifiedApp(_, _, args) => args
            .iter()
            .find_map(|arg| find_application_arg_sorts_with_locals(state, locals, arg, symbol)),
        Term::Let(bindings, body) => {
            let from_bindings = bindings.iter().find_map(|(_, term)| {
                find_application_arg_sorts_with_locals(state, locals, term, symbol)
            });
            let extended = extend_let_sort_locals(state, locals, bindings);
            from_bindings
                .or_else(|| find_application_arg_sorts_with_locals(state, &extended, body, symbol))
        }
        Term::Forall(bindings, body)
        | Term::Exists(bindings, body)
        | Term::Lambda(bindings, body) => {
            let extended = extend_sorted_sort_locals(locals, bindings);
            find_application_arg_sorts_with_locals(state, &extended, body, symbol)
        }
        Term::Annotated(inner, _) => {
            find_application_arg_sorts_with_locals(state, locals, inner, symbol)
        }
        Term::Const(_) | Term::Symbol(_) => None,
        _ => None,
    }
}

fn command_application_arg_sorts(
    state: &SmtTranscriptState,
    cmd: &Command,
    symbol: &str,
) -> Option<Vec<String>> {
    match cmd {
        Command::Assert(term) | Command::Simplify(term) | Command::Eval(term) => {
            find_application_arg_sorts(state, term, symbol)
        }
        Command::CheckSatAssuming(terms) => terms
            .iter()
            .find_map(|term| find_application_arg_sorts(state, term, symbol)),
        Command::GetValue(terms) => terms
            .iter()
            .find_map(|(_, term)| find_application_arg_sorts(state, term, symbol)),
        _ => None,
    }
}

fn is_smt_symbol_boundary(ch: char) -> bool {
    ch.is_whitespace() || matches!(ch, '(' | ')' | ';' | '"')
}

fn find_symbol_byte_offset(text: &str, symbol: &str) -> Option<usize> {
    text.match_indices(symbol).find_map(|(idx, _)| {
        let before_ok = text[..idx]
            .chars()
            .next_back()
            .map_or(true, is_smt_symbol_boundary);
        let after_idx = idx + symbol.len();
        let after_ok = text[after_idx..]
            .chars()
            .next()
            .map_or(true, is_smt_symbol_boundary);
        (before_ok && after_ok).then_some(idx)
    })
}

fn matching_close_paren(text: &str, open_idx: usize) -> Option<usize> {
    let mut depth = 0usize;
    let mut in_comment = false;
    let mut in_string = false;
    let mut chars = text[open_idx..].char_indices().peekable();

    while let Some((relative_idx, ch)) = chars.next() {
        let idx = open_idx + relative_idx;

        if in_comment {
            if ch == '\n' {
                in_comment = false;
            }
            continue;
        }

        if in_string {
            if ch == '"' {
                if let Some((_, '"')) = chars.peek().copied() {
                    let _ = chars.next();
                    continue;
                }
                in_string = false;
            }
            continue;
        }

        match ch {
            ';' => in_comment = true,
            '"' => in_string = true,
            '(' => depth = depth.saturating_add(1),
            ')' => {
                depth = depth.saturating_sub(1);
                if depth == 0 {
                    return Some(idx);
                }
            }
            _ => {}
        }
    }

    None
}

fn previous_non_whitespace(text: &str, before_idx: usize) -> Option<usize> {
    text[..before_idx]
        .char_indices()
        .rev()
        .find_map(|(idx, ch)| (!ch.is_whitespace()).then_some(idx))
}

fn find_application_last_arg_end(text: &str, symbol: &str) -> Option<usize> {
    text.match_indices(symbol).find_map(|(idx, _)| {
        if text[..idx].chars().next_back().is_none_or(|ch| ch != '(') {
            return None;
        }
        let after_idx = idx + symbol.len();
        if !text[after_idx..]
            .chars()
            .next()
            .is_some_and(is_smt_symbol_boundary)
        {
            return None;
        }

        let open_idx = idx.checked_sub(1)?;
        let close_idx = matching_close_paren(text, open_idx)?;
        let last_arg_idx = previous_non_whitespace(text, close_idx)?;
        (last_arg_idx >= after_idx).then_some(last_arg_idx)
    })
}

fn undefined_symbol_position(state: &SmtTranscriptState, symbol: &str) -> Option<SourcePosition> {
    let source = state.current_source.as_ref()?;
    let symbol_idx = find_symbol_byte_offset(&source.text, symbol)?;
    Some(z3_parser_symbol_position(
        state,
        source_position_at(source, symbol_idx),
    ))
}

fn undefined_application_position(
    state: &SmtTranscriptState,
    symbol: &str,
) -> Option<SourcePosition> {
    let source = state.current_source.as_ref()?;
    let last_arg_idx = find_application_last_arg_end(&source.text, symbol)?;
    Some(z3_parser_application_position(
        state,
        source_position_at(source, last_arg_idx),
    ))
}

fn z3_compat_undefined_symbol_error(
    state: &SmtTranscriptState,
    cmd: &Command,
    message: &str,
) -> Option<String> {
    let symbol = message
        .strip_prefix("elaboration error: undefined symbol: ")?
        .trim();
    if symbol.is_empty() {
        return None;
    }
    if let Some(arg_sorts) = command_application_arg_sorts(state, cmd, symbol) {
        let message = format!("unknown constant {} ({}) ", symbol, arg_sorts.join(" "));
        return Some(source_error(
            undefined_application_position(state, symbol)
                .or_else(|| undefined_symbol_position(state, symbol)),
            &message,
        ));
    }
    let message = format!("unknown constant {symbol}");
    Some(source_error(
        undefined_symbol_position(state, symbol),
        &message,
    ))
}

/// A `=`/`distinct`/theory-op **sort mismatch** — e.g. an ill-sorted
/// FloatingPoint equality between different `(_ FloatingPoint eb sb)` widths
/// (`#fp-sort-mismatch`), which AY otherwise bit-blasts into an index-out-of-
/// bounds panic in the FP gate — is reported the way z3 reports it: `(error
/// "...")` on **stdout**, with execution CONTINUING (the offending command is
/// dropped). Mirrors z3's `Sorts A and B are incompatible` wording. The caller
/// then taints the problem so a pending `check-sat` answers `unknown` (fail
/// closed; z3 emits `sat` on the incomplete remainder, AY is deliberately more
/// conservative). Returning the error on stdout + a verdict + rc 1 keeps the
/// "every check-sat emits a verdict" invariant — the previous stderr-and-abort
/// path exited 1 with an EMPTY verdict, the worst shape for a driver.
fn z3_compat_sort_mismatch_error(state: &SmtTranscriptState, message: &str) -> Option<String> {
    let detail = message.strip_prefix("elaboration error: sort mismatch: ")?;
    // `detail` is "expected {E}, got {A}"; re-render to z3's phrasing when the
    // shape matches, else pass the AY detail through verbatim.
    let rendered = match detail
        .strip_prefix("expected ")
        .and_then(|rest| rest.split_once(", got "))
    {
        Some((expected, actual)) => format!("Sorts {expected} and {actual} are incompatible"),
        None => detail.to_string(),
    };
    Some(source_error(
        current_source_last_token_position(state),
        &rendered,
    ))
}

fn maybe_handle_recoverable_execution_error(
    state: &mut SmtTranscriptState,
    cmd: &Command,
    message: &str,
) -> bool {
    if let Some(output) = z3_compat_undefined_symbol_error(state, cmd, message) {
        print_regular_line(state, &output);
        state.note_recoverable_error();
        return true;
    }
    if let Some(output) = z3_compat_sort_mismatch_error(state, message) {
        print_regular_line(state, &output);
        state.note_recoverable_error();
        return true;
    }
    // An unrecognized `(set-logic X)` is IGNORED with z3-identical output: the
    // token z3 does not recognize (validated in the executor via the same
    // structural predicate z3 uses) prints `unsupported` on stdout plus a
    // `; ignoring unsupported logic <TOK> line: <L> position: <P>` diagnostic
    // comment on stderr, then solving CONTINUES with ALL semantics and the exit
    // code is UNAFFECTED (z3 exits 0 on an ignored logic — so, unlike every
    // other recoverable error, this one does NOT call `note_recoverable_error`).
    // The logic is treated as never set (a later `set-logic` still succeeds).
    if let Command::SetLogic(logic) = cmd {
        let comment = format!(
            "; ignoring unsupported logic {logic} {}",
            match z3_unsupported_query_position(state) {
                Some(position) => format!("line: {} position: {}", position.line, position.column),
                None => "line: unsupported".to_string(),
            }
        );
        if state.regular_output_channel == state.diagnostic_output_channel {
            print_regular_line(state, &format!("unsupported\n{comment}"));
        } else {
            print_regular_line(state, "unsupported");
            print_diagnostic_line(state, &comment);
        }
        return true;
    }
    // General fail-closed routing for ANY OTHER elaboration error — datatype
    // member collision (`declare-const hd` when `hd` is a selector), reserved-
    // symbol declaration, sort redeclaration, and the like. Each is a SOUND
    // rejection of a malformed/conflating declaration (they prevent a wrong-
    // UNSAT conflation class), but a dropped problem-contributing command must
    // still leave a verdict: report the error on STDOUT and CONTINUE, so the
    // caller taints the session and the pending check-sat answers `unknown`,
    // rather than aborting the stream to an EMPTY verdict with the error only on
    // stderr (the worst shape for a driver). Mirrors z3's continued-execution;
    // the specific handlers above keep z3's exact wording for the common
    // undefined-symbol / sort-mismatch cases. (#every-check-sat-emits-a-verdict)
    if let Some(detail) = message.strip_prefix("elaboration error: ") {
        let output = source_error(current_source_last_token_position(state), detail);
        print_regular_line(state, &output);
        state.note_recoverable_error();
        return true;
    }
    false
}

fn exit_if_transcript_had_recoverable_error(state: &SmtTranscriptState) {
    if state.had_recoverable_error {
        let _ = io::stdout().flush();
        let _ = io::stderr().flush();
        std::process::exit(1);
    }
}

fn exit_if_timed_out_with_transcript_context(state: &SmtTranscriptState) {
    if is_timed_out() && state.had_recoverable_error && !z3_mode_enabled() {
        let count = state.recoverable_error_count.max(1);
        let plural = if count == 1 { "" } else { "s" };
        print_diagnostic_line(
            state,
            &format!(
                "; ay diagnostic: timeout occurred after {count} recoverable SMT-LIB error{plural}; input had already failed SMT-LIB execution before the timeout"
            ),
        );
    }
    exit_if_timed_out();
}

fn update_rlimit_after_command(state: &mut SmtTranscriptState, cmd: &Command) {
    match cmd {
        Command::Assert(_) => state.rlimit = state.rlimit.saturating_add(3),
        Command::CheckSat | Command::CheckSatAssuming(_) => {
            state.rlimit = state.rlimit.saturating_add(30);
        }
        Command::Push(_) | Command::Pop(_) | Command::Reset | Command::ResetAssertions => {
            state.rlimit = state.rlimit.saturating_add(1);
        }
        _ => {}
    }
}

fn update_transcript_state_after_command(state: &mut SmtTranscriptState, cmd: &Command) {
    update_rlimit_after_command(state, cmd);

    match cmd {
        Command::SetOption(keyword, value) if keyword_key(keyword) == "print-success" => {
            if let Some(enabled) = sexpr_bool(value) {
                state.print_success = enabled;
            }
        }
        // `:produce-assertions` is the SMT-LIB 2.6 name; `:interactive-mode` is
        // its deprecated 2.5 synonym. Both enable `(get-assertions)`. z3 uses
        // `:produce-assertions`, so accept either (matches z3). (#get-assertions)
        Command::SetOption(keyword, value)
            if matches!(
                keyword_key(keyword),
                "interactive-mode" | "produce-assertions"
            ) =>
        {
            if let Some(enabled) = sexpr_bool(value) {
                state.interactive_mode = enabled;
            }
        }
        Command::SetOption(keyword, value) if keyword_key(keyword) == "produce-assignments" => {
            if let Some(enabled) = sexpr_bool(value) {
                state.produce_assignments = enabled;
            }
        }
        Command::SetOption(keyword, value) if keyword_key(keyword) == "produce-proofs" => {
            if let Some(enabled) = sexpr_bool(value) {
                state.produce_proofs = enabled;
            }
        }
        Command::SetOption(keyword, value)
            if keyword_key(keyword) == "produce-unsat-assumptions" =>
        {
            if let Some(enabled) = sexpr_bool(value) {
                state.produce_unsat_assumptions = enabled;
            }
        }
        Command::SetOption(keyword, value) if is_global_decls_option(keyword_key(keyword)) => {
            if let Some(enabled) = sexpr_bool(value) {
                state.global_decls = enabled;
            }
        }
        Command::SetOption(keyword, value) if keyword_key(keyword) == "auto-config" => {
            if let Some(enabled) = sexpr_bool(value) {
                state.auto_config = enabled;
            }
        }
        Command::SetOption(keyword, value) if keyword_key(keyword) == "model.v2" => {
            if let Some(enabled) = sexpr_bool(value) {
                state.model_v2 = enabled;
            }
        }
        Command::SetOption(keyword, value) if keyword_key(keyword) == "model.compact" => {
            if let Some(enabled) = sexpr_bool(value) {
                state.model_compact = enabled;
            }
        }
        Command::SetOption(keyword, value) if keyword_key(keyword) == "pp.decimal" => {
            if let Some(enabled) = sexpr_bool(value) {
                state.pp_decimal = enabled;
            }
        }
        Command::SetOption(keyword, value) if keyword_key(keyword) == "pp.decimal-precision" => {
            if let Some(precision) = sexpr_numeral(value) {
                state.pp_decimal_precision = precision.to_string();
            }
        }
        Command::SetOption(keyword, value) if keyword_key(keyword) == "pp.max-depth" => {
            if let Some(depth) = sexpr_numeral(value) {
                state.pp_max_depth = depth.to_string();
            }
        }
        Command::SetOption(keyword, value) if keyword_key(keyword) == "pp.max-ribbon" => {
            if let Some(ribbon) = sexpr_numeral(value) {
                state.pp_max_ribbon = ribbon.to_string();
            }
        }
        Command::SetOption(keyword, value) if keyword_key(keyword) == "pp.single-line" => {
            if let Some(enabled) = sexpr_bool(value) {
                state.pp_single_line = enabled;
            }
        }
        Command::SetOption(keyword, value) if keyword_key(keyword) == "pp.bv-literals" => {
            if let Some(enabled) = sexpr_bool(value) {
                state.pp_bv_literals = enabled;
            }
        }
        Command::SetOption(keyword, value) if keyword_key(keyword) == "regular-output-channel" => {
            if let Some(channel) = sexpr_string(value) {
                prepare_transcript_channel(channel);
                state.regular_output_channel = channel.to_string();
            }
        }
        Command::SetOption(keyword, value)
            if keyword_key(keyword) == "diagnostic-output-channel" =>
        {
            if let Some(channel) = sexpr_string(value) {
                prepare_transcript_channel(channel);
                state.diagnostic_output_channel = channel.to_string();
            }
        }
        Command::SetOption(keyword, value) if keyword_key(keyword) == "verbosity" => {
            if let Some(verbosity) = sexpr_numeral(value) {
                state.verbosity = verbosity.to_string();
            }
        }
        Command::SetOption(keyword, value) if keyword_key(keyword) == "rlimit" => {
            if let Some(rlimit) = sexpr_numeral(value) {
                state.rlimit_option = rlimit.to_string();
            }
        }
        Command::SetOption(keyword, value) if is_z3_compat_bool_option(keyword_key(keyword)) => {
            if let Some(enabled) = sexpr_bool(value) {
                state
                    .z3_compat_bool_options
                    .insert(keyword_key(keyword).to_string(), enabled);
            }
        }
        Command::SetInfo(keyword, value) if keyword_key(keyword) == "status" => {
            if let Some(status) = sexpr_status(value) {
                state.status = Some(status.to_string());
            }
        }
        Command::DeclareConst(name, sort) => {
            state.symbol_sorts.insert(name.clone(), sort_text(sort));
        }
        Command::DeclareFun(name, args, sort) if args.is_empty() => {
            state.symbol_sorts.insert(name.clone(), sort_text(sort));
        }
        Command::DefineFun(name, _, sort, _) | Command::DefineFunRec(name, _, sort, _) => {
            state.symbol_sorts.insert(name.clone(), sort_text(sort));
        }
        Command::Push(depth) => {
            state.assertion_stack_depth = state.assertion_stack_depth.saturating_add(*depth);
            state.executor_assertion_stack_depth =
                state.executor_assertion_stack_depth.saturating_add(*depth);
        }
        Command::Pop(depth) => {
            state.assertion_stack_depth = state.assertion_stack_depth.saturating_sub(*depth);
            state.executor_assertion_stack_depth =
                state.executor_assertion_stack_depth.saturating_sub(*depth);
        }
        Command::Reset => {
            state.assertion_stack_depth = 0;
            state.executor_assertion_stack_depth = 0;
            state.symbol_sorts.clear();
            // SMT-LIB 2.6: `(reset)` returns the solver to its initial state, so
            // it must also clear the fail-closed poison a prior recoverable error
            // set. Without this, a dropped problem-contributing command latched
            // every later `check-sat` to `unknown` FOREVER — even for a fresh,
            // fully-valid problem built after the reset — where z3 answers
            // sat/unsat. Clearing here is sound: everything from before the reset
            // (including the dropped command) is gone, so the poison no longer
            // applies. NB: only `(reset)` is a full fresh start;
            // `(reset-assertions)` keeps declarations, so its poison is left
            // intact (a dropped declaration can still matter).
            state.completeness = ProblemCompleteness::Complete;
            state.had_recoverable_error = false;
            state.recoverable_error_count = 0;
        }
        Command::ResetAssertions => {
            state.executor_assertion_stack_depth = 0;
        }
        _ => {}
    }
}

fn maybe_print_success(state: &SmtTranscriptState) {
    if state.print_success {
        print_regular_line(state, "success");
    }
}

fn unsupported_get_info_parameters() -> &'static str {
    "unsupported\n; Suppported get-info parameters:\n; (get-info :reason-unknown)\n; (get-info :status)\n; (get-info :version)\n; (get-info :authors)\n; (get-info :error-behavior)\n; (get-info :parameters)\n; (get-info :rlimit)\n; (get-info :assertion-stack-levels)"
}

/// Z3 version reported under explicit `--z3-mode` (full impersonation). Matches
/// the cached Z3 baseline that `ay --z3-mode` is documented and smoke-tested
/// against (the development design notes). Kept in sync with that baseline.
const Z3_COMPAT_BASELINE_VERSION: &str = "4.15.4";

fn z3_compat_get_info_output(
    state: &SmtTranscriptState,
    keyword: &str,
    output: &str,
) -> Option<String> {
    match keyword_key(keyword) {
        "status" => Some(format!(
            "(:status {})",
            state.status.as_deref().unwrap_or("unknown")
        )),
        "rlimit" => Some(format!("(:rlimit {})", state.rlimit)),
        "assertion-stack-levels" => Some(format!(
            "(:assertion-stack-levels {})",
            state.assertion_stack_depth
        )),
        "name" => Some("(:name \"Z3\")".to_string()),
        "authors" => Some(
            "(:authors \"Leonardo de Moura, Nikolaj Bjorner, Lev Nachmanson and Christoph Wintersteiger\")"
                .to_string(),
        ),
        // Explicit `--z3-mode` is opt-in full Z3 impersonation: this filter
        // already reports `:name "Z3"` and Z3's authors, and the mode is
        // documented (the development design notes) to match a cached Z3 4.15.4
        // baseline. Report a matching Z3 version so the identity triple
        // (name/authors/version) is internally consistent and tools that gate
        // on the Z3 version see a real one. Plain `-in` (no --z3-mode)
        // deliberately keeps AY's own build provenance instead (honest default,
        // see tests in group_cli/z3_compat_args.rs).
        "version" if z3_mode_enabled() => {
            Some(format!("(:version \"{Z3_COMPAT_BASELINE_VERSION}\")"))
        }
        "parameters" => None,
        "error-behavior" => Some("(:error-behavior continued-execution)".to_string()),
        "reason-unknown" if output == "(error \"no unknown result to explain\")" => Some(
            "(:reason-unknown \"state of the most recent check-sat command is not known\")"
                .to_string(),
        ),
        // Under explicit `--z3-mode` (full Z3 impersonation), remap AY's native
        // reason-unknown vocabulary — which is cvc5/yices-style (`resourceout`,
        // `memout`, bare `incomplete`, `unsupported`, ...) — to Z3's exact
        // strings. A real Z3 consumer parses `(:reason-unknown ...)` by literal
        // match: Verus, for one, only accepts `"canceled"`, `"unknown"`, or an
        // `"(incomplete...` prefix and PANICS on anything else. Native `-in`
        // (no --z3-mode) keeps AY's own descriptive reasons (ay-first mode).
        "reason-unknown" if z3_mode_enabled() => Some(
            reason_unknown_inner(output)
                .map(z3_reason_unknown_output)
                .unwrap_or_else(|| output.to_string()),
        ),
        _ if output.starts_with("(error \"unsupported info keyword:") => {
            if state.regular_output_channel == state.diagnostic_output_channel {
                let comment = z3_unsupported_query_comment(state, keyword);
                let parameters = unsupported_get_info_parameters();
                let (head, tail) = parameters
                    .split_once('\n')
                    .unwrap_or((parameters, ""));
                return Some(format!("{head}\n{comment}\n{tail}"));
            }
            eprintln_z3_unsupported_query_comment(state, keyword);
            Some(unsupported_get_info_parameters().to_string())
        }
        _ => Some(output.to_string()),
    }
}

fn z3_mode_enabled() -> bool {
    Z3_MODE_ENABLED.load(std::sync::atomic::Ordering::Relaxed)
}

fn z3_model_enabled() -> bool {
    Z3_MODEL_ENABLED.load(std::sync::atomic::Ordering::Relaxed)
}

/// Extract the reason token from AY's native `(:reason-unknown <r>)` output.
///
/// AY prints the reason UNQUOTED (its `UnknownReason` `Display`), e.g.
/// `(:reason-unknown incomplete)` or `(:reason-unknown (incomplete
/// quantifier-cegqi))`; the token itself may contain spaces and parens. Returns
/// `None` if `output` is not in that shape (leaving it untouched).
fn reason_unknown_inner(output: &str) -> Option<&str> {
    output
        .strip_prefix("(:reason-unknown ")
        .and_then(|rest| rest.strip_suffix(')'))
}

/// Rewrite AY's native reason-unknown token `inner` (its `UnknownReason`
/// `Display`, cvc5/yices-style) into a `(:reason-unknown "...")` line using
/// Z3's vocabulary, for `--z3-mode` drop-in consumers.
///
/// The mapping is fail-closed and preserves the sat/unsat verdict (this only
/// touches how an `unknown` is *explained*):
///   * resource / time / memory / interrupt exhaustion -> Z3's `"canceled"`
///     (Z3 reports rlimit/timeout as canceled; Verus treats it as retryable);
///   * Z3's own `"unknown"` is kept verbatim (Verus accepts it);
///   * anything already in `(incomplete ...)` form is kept (matches Z3's
///     incompleteness prefix);
///   * every other reason (bare `incomplete`, `unsupported*`, `internal-error`,
///     ...) is wrapped as `(incomplete <reason>)` so a consumer treats the goal
///     as NOT proved — the sound default — while preserving AY's detail.
fn z3_reason_unknown_output(inner: &str) -> String {
    let z3 = match inner {
        "timeout" | "resourceout" | "memout" | "interrupted" => "canceled".to_string(),
        "unknown" => "unknown".to_string(),
        s if s.starts_with("(incomplete") => s.to_string(),
        "incomplete" => "(incomplete)".to_string(),
        other => format!("(incomplete {other})"),
    };
    format!("(:reason-unknown \"{z3}\")")
}

fn simple_get_option_value<'a>(key: &str, output: &'a str) -> Option<&'a str> {
    let prefix = format!("(:{key} ");
    output.strip_prefix(&prefix)?.strip_suffix(')')
}

fn z3_compat_bool_option_defaults() -> HashMap<String, bool> {
    [
        ("ctrl-c", true),
        ("model.completion", false),
        ("model.partial", false),
        ("model_validate", false),
        ("unsat_core", false),
        ("type-check", true),
        ("well-sorted-check", false),
        ("debug-ref-count", false),
        ("trace", false),
        ("dump-models", false),
        ("stats", false),
    ]
    .into_iter()
    .map(|(key, value)| (key.to_string(), value))
    .collect()
}

fn is_z3_compat_bool_option(key: &str) -> bool {
    matches!(
        key,
        "ctrl-c"
            | "model.completion"
            | "model.partial"
            | "model_validate"
            | "unsat_core"
            | "type-check"
            | "well-sorted-check"
            | "debug-ref-count"
            | "trace"
            | "dump-models"
            | "stats"
    )
}

fn z3_compat_get_option_output(
    state: &SmtTranscriptState,
    keyword: &str,
    output: &str,
) -> Option<String> {
    let key = keyword_key(keyword);
    if key == "interactive-mode" || key == "produce-assertions" {
        return Some(state.interactive_mode.to_string());
    }
    if key == "produce-assignments" {
        return Some(state.produce_assignments.to_string());
    }
    if key == "produce-unsat-assumptions" {
        return Some(state.produce_unsat_assumptions.to_string());
    }
    if is_global_decls_option(key) {
        return Some(state.global_decls.to_string());
    }
    if key == "auto-config" {
        return Some(state.auto_config.to_string());
    }
    if key == "model.v2" {
        return Some(state.model_v2.to_string());
    }
    if key == "model.compact" {
        return Some(state.model_compact.to_string());
    }
    if key == "pp.decimal" {
        return Some(state.pp_decimal.to_string());
    }
    if key == "pp.decimal-precision" {
        return Some(state.pp_decimal_precision.clone());
    }
    if key == "pp.max-depth" {
        return Some(state.pp_max_depth.clone());
    }
    if key == "pp.max-ribbon" {
        return Some(state.pp_max_ribbon.clone());
    }
    if key == "pp.single-line" {
        return Some(state.pp_single_line.to_string());
    }
    if key == "pp.bv-literals" {
        return Some(state.pp_bv_literals.to_string());
    }
    if key == "regular-output-channel" {
        return Some(state.regular_output_channel.clone());
    }
    if key == "diagnostic-output-channel" {
        return Some(state.diagnostic_output_channel.clone());
    }
    if key == "verbosity" {
        return Some(state.verbosity.clone());
    }
    if key == "rlimit" {
        return Some(state.rlimit_option.clone());
    }
    if let Some(value) = state.z3_compat_bool_options.get(key) {
        return Some(value.to_string());
    }

    if key == "timeout" && output == "(error \"unknown option: :timeout\")" {
        return Some("4294967295".to_string());
    }

    if output.starts_with("(error \"unknown option:") {
        if state.regular_output_channel == state.diagnostic_output_channel {
            return Some(format!(
                "unsupported\n{}",
                z3_unsupported_query_comment(state, keyword)
            ));
        }
        eprintln_z3_unsupported_query_comment(state, keyword);
        return Some("unsupported".to_string());
    }

    Some(match key {
        "produce-models"
        | "produce-unsat-cores"
        | "produce-proofs"
        | "produce-assignments"
        | "produce-unsat-assumptions"
        | "global-decls"
        | "auto-config"
        | "pp.decimal"
        | "pp.decimal-precision"
        | "pp.max-depth"
        | "pp.max-ribbon"
        | "regular-output-channel"
        | "diagnostic-output-channel"
        | "print-success"
        | "random-seed"
        | "verbosity"
        | "rlimit"
        | "ctrl-c"
        | "model_validate"
        | "unsat_core"
        | "type-check"
        | "well-sorted-check"
        | "debug-ref-count"
        | "trace"
        | "dump-models"
        | "stats"
        | "timeout" => simple_get_option_value(key, output)
            .map(str::to_string)
            .unwrap_or_else(|| output.to_string()),
        _ => output.to_string(),
    })
}

fn maybe_enable_z3_default_assignment_query(executor: &mut Executor, cmd: &Command) -> bool {
    if !matches!(cmd, Command::GetAssignment) {
        return true;
    }

    executor
        .execute(&Command::SetOption(
            ":produce-assignments".to_string(),
            SExpr::True,
        ))
        .is_ok()
}

fn z3_compat_output_for_command(
    state: &mut SmtTranscriptState,
    cmd: &Command,
    output: &str,
) -> Option<String> {
    match cmd {
        Command::GetInfo(keyword) => z3_compat_get_info_output(state, keyword, output),
        Command::GetOption(keyword) => z3_compat_get_option_output(state, keyword, output),
        Command::GetModel if output == "(error \"model generation is not enabled\")" => {
            state.note_recoverable_error();
            Some(source_error(
                current_source_last_token_position(state),
                "model is not available",
            ))
        }
        Command::GetModel if z3_mode_enabled() && output.starts_with("(model\n") => {
            // z3 4.15.4 and SMT-LIB 2.6 emit get-model as a bare
            // `( <define-fun>* )` sequence; AY's native form prepends a `model`
            // head symbol (a legacy pre-4.8 z3 convention that a strict 2.6
            // reader rejects). --z3-mode exists to produce byte-compatible
            // transcripts, so drop the head. Printer-only: the define-fun body
            // is untouched and both forms parse to the identical model, so this
            // cannot change any verdict. (AY's internal model parsers consume
            // the native `(model …)` form upstream of this CLI print boundary,
            // so they are unaffected.)
            Some(format!("(\n{}", &output["(model\n".len()..]))
        }
        Command::GetValue(_) if output == "(error \"model is not available\")" => {
            state.note_recoverable_error();
            Some(source_error(
                current_source_last_token_position(state),
                "model is not available",
            ))
        }
        Command::GetUnsatCore
            if output
                == "(error \"unsat core generation is not enabled, set :produce-unsat-cores to true\")" =>
        {
            state.note_recoverable_error();
            Some(source_error(
                current_source_last_token_position(state),
                "unsat core construction is not enabled, use command (set-option :produce-unsat-cores true)",
            ))
        }
        Command::GetUnsatAssumptions
            if output == "(error \"no check-sat-assuming has been performed\")" =>
        {
            Some("()".to_string())
        }
        Command::GetUnsatAssumptions
            if output == "(error \"unsat assumptions not available, last result was sat\")" =>
        {
            state.note_recoverable_error();
            Some(source_error(
                current_source_last_token_position(state),
                "unsat assumptions is not available",
            ))
        }
        _ => Some(output.to_string()),
    }
}

/// Finalize `--decision-trace` for SMT-LIB runs.
///
/// The SAT solver owns the `DecisionTraceWriter` and emits the canonical
/// MAGIC + VERSION + event stream whenever it reaches CDCL. On preprocessing-
/// only UNSAT (e.g., two contradictory unit assertions reduced by Tseitin /
/// early propagation) the DPLL(T) pipeline can short-circuit before the SAT
/// solver is ever constructed — leaving the trace file absent and breaking
/// `--replay` round-trip.
///
/// After SMT execution finishes, if `--decision-trace` was requested and no
/// file exists at the path (or the file is zero bytes), write a minimal valid
/// trace consisting of MAGIC + VERSION + a single `Result` event reflecting
/// the executor's last verdict. This guarantees `--replay` consumers always
/// see a terminal outcome event.
///
/// Part of `EXPLAINABILITY_AUDIT.md` Finding B.
fn maybe_write_minimal_decision_trace(executor: &Executor) {
    let Some(path) = ay_core::trace_config().decision_trace_path.as_deref() else {
        return;
    };
    // Only overwrite when the solver-owned writer produced no bytes.
    // Any populated file (even a solver-terminated minimal trace) is left
    // untouched so we never clobber real event data.
    match std::fs::metadata(path) {
        Ok(meta) if meta.len() > 0 => return,
        Ok(_) => {} // zero-byte file — fall through and rewrite
        Err(err) if err.kind() == io::ErrorKind::NotFound => {} // no file — write one
        Err(err) => {
            safe_eprintln!(
                "warning: cannot stat decision-trace file {path}: {err} (skipping minimal fallback)"
            );
            return;
        }
    }
    let outcome = if executor.last_result_is_unsat() {
        ay_sat::TraceOutcome::Unsat
    } else if executor.last_result_is_unknown() {
        ay_sat::TraceOutcome::Unknown
    } else {
        ay_sat::TraceOutcome::Sat
    };
    if let Err(err) = ay_sat::write_minimal_trace(path, outcome) {
        safe_eprintln!("warning: failed to write minimal decision trace {path}: {err}");
    }
}

/// Inspect the executor's last Alethe proof and return `true` when the
/// terminal empty-clause derivation rides on an unverified `:rule trust`
/// fallback (either `AletheRule::Trust` or a trust-emitting
/// `TheoryLemmaKind`, e.g. `Generic`). See #8759.
fn terminal_trust_detected(executor: &Executor) -> bool {
    let trust_or_hole = executor
        .last_proof()
        .map(|p| ay_proof::terminal_trust_report(p).has_terminal_trust())
        .unwrap_or(false);
    // Leak-2: also downgrade when the terminal derivation rides on an `assume`
    // NOT backed by the problem's provenance (a laundered free axiom). The
    // provenance set is executor state (original assertions + quantifier
    // expansions), so the check lives on the executor.
    //
    // TIER-0 leak: also downgrade when the proof references sequence-theory
    // content (`Seq`-sorted terms). Such a proof can be clean (zero hole/trust,
    // no foreign assume — e.g. a `seq.nth` term forced to two distinct integer
    // constants collapses to a pure `la_generic`/`resolution` chain) yet is NOT
    // independently checkable: carcara cannot parse the `Seq` sort, no
    // firewall-Lean lemma covers sequences, and there is no DRAT lane. Shipping
    // it bare under `--strict-proofs` would accept an uncheckable proof, a
    // §0-class certification leak.
    trust_or_hole
        || executor.unsat_proof_terminal_foreign_assume()
        || executor.unsat_proof_references_uncheckable_seq_theory()
}

/// Execute a command and print the result.
///
/// This centralizes executor.execute result handling to avoid duplication.
/// Output is printed to stdout, errors to stderr in SMT-LIB format.
///
/// Per SMT-LIB 2.6, when check-sat returns "unknown", the solver SHOULD
/// emit `(:reason-unknown ...)` so the user knows why satisfiability could
/// not be determined. We emit this to stderr automatically after printing
/// the "unknown" result to stdout.
/// z3's exact redefinition error text if `cmd` redeclares/redefines an existing
/// name in a way z3 4.15.4 rejects, else `None`. Covers `declare-const`,
/// `declare-fun`, `define-fun`, `define-fun-rec`, and `define-funs-rec` (each
/// with z3's distinct collision/overload rules); the message BODY is returned
/// (the CLI prepends the source position). See the call site in
/// [`execute_and_print`] for the full z3-parity rationale.
fn redefinition_error_for_command(executor: &mut Executor, cmd: &Command) -> Option<String> {
    match cmd {
        Command::DeclareConst(name, sort) => {
            executor
                .context_mut()
                .redefinition_error(IntroKind::Declare, name, &[], sort)
        }
        Command::DeclareFun(name, args, ret) => {
            executor
                .context_mut()
                .redefinition_error(IntroKind::Declare, name, args, ret)
        }
        Command::DefineFun(name, params, ret, _) => {
            let arg_sorts: Vec<_> = params.iter().map(|(_, s)| s.clone()).collect();
            executor
                .context_mut()
                .redefinition_error(IntroKind::Macro, name, &arg_sorts, ret)
        }
        Command::DefineFunRec(name, params, ret, _) => {
            let arg_sorts: Vec<_> = params.iter().map(|(_, s)| s.clone()).collect();
            executor
                .context_mut()
                .redefinition_error(IntroKind::Recursive, name, &arg_sorts, ret)
        }
        Command::DefineFunsRec(decls, _) => {
            // A batch defines several names at once; z3 reports the first that
            // collides. Check each against the pre-command context.
            for (name, params, ret) in decls {
                let arg_sorts: Vec<_> = params.iter().map(|(_, s)| s.clone()).collect();
                if let Some(msg) = executor.context_mut().redefinition_error(
                    IntroKind::Recursive,
                    name,
                    &arg_sorts,
                    ret,
                ) {
                    return Some(msg);
                }
            }
            None
        }
        _ => None,
    }
}

fn execute_and_print(
    executor: &mut Executor,
    cmd: &Command,
    transcript: &mut SmtTranscriptState,
    // z3 `-model` inline emission: only the streaming path sets this. The
    // non-incremental file path appends a literal `(get-model)` instead, so it
    // passes false to avoid emitting the model twice.
    emit_z3_model_inline: bool,
) -> bool {
    if ay_core::trace_config().dump_bv_cnf_path.is_some()
        && matches!(
            cmd,
            Command::SetOption(keyword, _)
                if matches!(
                    keyword_key(keyword),
                    "regular-output-channel" | "diagnostic-output-channel"
                )
        )
    {
        if let Err(error) = Executor::invalidate_bv_cnf_export_for_rejected_check() {
            eprintln_smt_error(error.to_string());
        } else {
            eprintln_smt_error(
                "artifact export failed: --dump-bv-cnf forbids dynamic SMT-LIB output channels because they can overwrite or append to the certificate",
            );
        }
        transcript.note_recoverable_error();
        return false;
    }

    if maybe_handle_cli_transcript_command(transcript, cmd) {
        return true;
    }

    // z3 4.15.4 rejects a redeclaration/redefinition of a name that collides
    // with an existing binding: e.g. `invalid declaration, <kind> '<name>'
    // (with the given signature) already declared` for a same-signature
    // declare, `named expression already defined` for a `define-fun` macro,
    // etc. The offending command is DROPPED (the original binding survives),
    // execution continues, and the run exits 1 at EOF. Overloads z3 permits
    // (a different signature, or a recfun/declare cross pair) are accepted. We
    // detect this at the text-command layer, BEFORE executor.execute, so the
    // programmatic ay-dpll declare_fun path — whose idempotent same-signature
    // redeclare adopts the existing handle — is left untouched. No taint is
    // applied: dropping the redeclaration keeps the original binding, so a
    // pending check-sat retains full z3 verdict parity (e.g. `(= x 1)` then a
    // dropped redeclare then `(= x 2)` is unsat over the SAME x, not a
    // fresh-var sat). See [`redefinition_error_for_command`] for the exact
    // collision matrix. (#P0.3)
    if let Some(message) = redefinition_error_for_command(executor, cmd) {
        print_regular_line(
            transcript,
            &source_error(current_source_last_token_position(transcript), &message),
        );
        transcript.note_recoverable_error();
        return true;
    }

    // z3 ACCEPTS a `declare-const`/`declare-fun` whose name is already a
    // recursive function (`define-fun-rec`/`define-funs-rec`): it creates an
    // overload and resolves each later reference per-signature (emitting an
    // `ambiguous constant reference` error only when a use is truly ambiguous).
    // AY keeps a single binding per name and cannot represent that overload —
    // it would silently resolve later uses to the wrong `g` and can answer
    // `unsat` where z3 answers `sat`. Since we cannot reproduce z3's semantics
    // soundly, fail closed: mark the problem incomplete so the pending
    // check-sat degrades to `unknown` (always sound) instead of a wrong verdict.
    // This is malformed input z3 itself flags; `unknown` beats a wrong `unsat`.
    // (#P0.3)
    if let Command::DeclareConst(name, _) | Command::DeclareFun(name, _, _) = cmd {
        if executor.context_mut().is_recursive_fun(name) {
            transcript.mark_incomplete();
        }
    }

    // (get-interpolant A B) / (compute-interpolant A B) are computed by the
    // ay-chc Craig/Farkas machinery, which the DPLL(T) executor cannot reach.
    // Intercept them here, before executor.execute(), using the declared sorts
    // from the elaboration context.
    if let Command::GetInterpolant(a, b) | Command::ComputeInterpolant(a, b) = cmd {
        print_regular_line(transcript, &compute_interpolant_output(executor, a, b));
        update_transcript_state_after_command(transcript, cmd);
        return true;
    }

    // SOUNDNESS BACKSTOP (#match-soundness, Part 1): if any problem-contributing
    // command was discarded (failed to parse or elaborate), the executor's
    // assertion set is an incomplete subset of the real problem. A dropped
    // constraint can only flip UNSAT into SAT, so a decision query must fail
    // closed to `unknown` rather than answer definitively on the remainder.
    // Generic over the discarded construct, so this class of unsoundness cannot
    // recur for ANY unsupported syntax.
    if transcript.is_incomplete() && matches!(cmd, Command::CheckSat | Command::CheckSatAssuming(_))
    {
        if let Err(error) = Executor::invalidate_bv_cnf_export_for_rejected_check() {
            eprintln_smt_error(error.to_string());
            return false;
        }
        if ay_core::trace_config().dump_bv_cnf_path.is_some() {
            eprintln_smt_error(
                "artifact export failed: --dump-bv-cnf cannot certify a transcript after a problem-contributing command was discarded",
            );
            return false;
        }
        update_transcript_state_after_command(transcript, cmd);
        print_regular_line(transcript, "unknown");
        super::VERDICT_PRINTED.store(true, std::sync::atomic::Ordering::SeqCst);
        if !z3_mode_enabled() {
            print_diagnostic_line(
                transcript,
                "(:reason-unknown \"a problem-contributing command was discarded\")",
            );
        }
        return true;
    }

    if !maybe_enable_z3_default_assignment_query(executor, cmd) {
        eprintln_smt_error("failed to enable assignment collection for get-assignment".to_string());
        return false;
    }

    // Competition robustness: an internal solver bug must NEVER crash the process
    // (a panic = the whole file/run dies = strictly worse than a wrong answer).
    // Catch any unwinding panic during execution and convert it to a sound,
    // non-crashing outcome — `unknown` for a decision query (always sound), a
    // recoverable `(error ...)` otherwise — then continue with the remaining
    // commands. The release profile is intentionally `panic = "unwind"` so this
    // containment works. Found by the diff_fuzz seq sort-interning crash (a valid
    // QF_SLIA input panicked `mk_eq expects same sort`, exiting the process 101).
    let exec_result = match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        executor.execute(cmd)
    })) {
        Ok(r) => r,
        Err(_panic) => {
            if matches!(cmd, Command::CheckSat | Command::CheckSatAssuming(_)) {
                if ay_core::trace_config().dump_bv_cnf_path.is_some() {
                    if let Err(error) = Executor::invalidate_bv_cnf_export_for_rejected_check() {
                        eprintln_smt_error(error.to_string());
                    } else {
                        eprintln_smt_error(
                                "artifact export failed: solver panicked before the current BV CNF certificate could be finalized",
                            );
                    }
                    return false;
                }
                print_regular_line(transcript, "unknown");
                super::VERDICT_PRINTED.store(true, std::sync::atomic::Ordering::SeqCst);
            } else {
                print_regular_line(transcript, "(error \"internal solver error\")");
            }
            update_transcript_state_after_command(transcript, cmd);
            return true;
        }
    };
    match exec_result {
        Ok(Some(output)) => {
            // Strict-proof mode: downgrade UNSAT to Unknown when the terminal
            // derivation chain contains a `:rule trust` fallback (#8759).
            // The proof is generated internally regardless of `--proof` because
            // `new_executor()` forces `set_produce_proofs(true)` under strict.
            if output == "unsat" && strict_proofs_enabled() && terminal_trust_detected(executor) {
                print_regular_line(transcript, "unknown");
                super::VERDICT_PRINTED.store(true, std::sync::atomic::Ordering::SeqCst);
                if !z3_mode_enabled() {
                    print_diagnostic_line(
                        transcript,
                        "(:reason-unknown (incomplete proof-trusted))",
                    );
                }
                return true;
            }
            // Verified-firewall self-cert gate (`--verify-firewall`): emit an
            // `unsat` only if AY can reconstruct at least one per-theory firewall
            // Lean proof AND every one kernel-checks under the real Lean
            // toolchain. Otherwise downgrade to a sound `unknown` (downgrading
            // unsat→unknown is always sound). Per-lemma PASS/FAIL goes to stderr.
            if output == "unsat" && verify_firewall_enabled() {
                match firewall_verify::verify_firewall_for_unsat(executor) {
                    FirewallVerdict::Certified { results } => {
                        firewall_verify::report(&results, true);
                        // Fall through: keep the `unsat`, now self-certified.
                    }
                    FirewallVerdict::NotCertified { reason, results } => {
                        firewall_verify::report(&results, false);
                        print_regular_line(transcript, "unknown");
                        super::VERDICT_PRINTED.store(true, std::sync::atomic::Ordering::SeqCst);
                        if !z3_mode_enabled() {
                            print_diagnostic_line(
                                transcript,
                                &format!("(:reason-unknown {reason})"),
                            );
                        }
                        return true;
                    }
                }
            }
            let raw_output = output;
            let rendered_output = z3_compat_output_for_command(transcript, cmd, &raw_output);
            update_transcript_state_after_command(transcript, cmd);
            if let Some(output) = rendered_output {
                print_regular_line(transcript, &output);
                // #verdict-latch: once ANY verdict (sat/unsat/unknown) is on
                // stdout, the timeout/SIGTERM fallbacks must never print a
                // second, potentially contradictory one. Found via QF_ALIA
                // pp-dmem2: the arrays->LIA rescue's `unsat` was followed by
                // a synthesized `unknown` when the internal timeout fired
                // during default-proof materialization.
                if matches!(raw_output.as_str(), "sat" | "unsat" | "unknown") {
                    super::mark_verdict_printed();
                }
            }
            // SMT-LIB compliance: emit reason-unknown to stderr when
            // check-sat produces "unknown", so users always know why.
            if raw_output == "unknown" {
                // Mark that "unknown" has been printed to prevent duplicate
                // output from exit_if_timed_out (#8674).
                super::VERDICT_PRINTED.store(true, std::sync::atomic::Ordering::SeqCst);
                if !z3_mode_enabled() {
                    if let Some(reason) = executor.get_reason_unknown() {
                        print_diagnostic_line(transcript, &format!("(:reason-unknown {reason})"));
                    } else {
                        print_diagnostic_line(transcript, "(:reason-unknown unknown)");
                    }
                }
            }
            // z3 `-model`: emit the model after a satisfiable `check-sat`, as if
            // `(get-model)` followed. Streaming/incremental only (the file path
            // appends a literal `(get-model)`); output-only, verdict unchanged.
            if emit_z3_model_inline
                && z3_model_enabled()
                && matches!(cmd, Command::CheckSat | Command::CheckSatAssuming(_))
                && executor.last_result_is_sat()
            {
                if let Ok(Some(mut model)) = executor.execute(&Command::GetModel) {
                    if !model.trim_start().starts_with("(error") {
                        // Same head-strip as the explicit-`(get-model)` path: z3
                        // 4.15.4 / SMT-LIB 2.6 emit a bare `( <define-fun>* )`,
                        // not AY's legacy `(model …)` head. Printer-only.
                        if z3_mode_enabled() && model.starts_with("(model\n") {
                            model = format!("(\n{}", &model["(model\n".len()..]);
                        }
                        print_regular_line(transcript, &model);
                    }
                }
            }
            true
        }
        Ok(None) => {
            update_transcript_state_after_command(transcript, cmd);
            maybe_print_success(transcript);
            true
        }
        Err(e) => {
            let message = e.to_string();
            // Resource limit while expanding a `define-fun-rec` over a symbolic
            // argument (unbounded unfolding). z3 decides these with real
            // recursive-function support; AY cannot unfold an unbounded recursion.
            // Exiting 1 with NO verdict on stdout is the worst possible shape for
            // a driver, so instead taint the problem to fail closed: the pending
            // `check-sat` answers `unknown` (always sound — a dropped constraint
            // can only turn UNSAT into SAT) via the generic is_incomplete() gate,
            // and the run still exits 0. The concrete/ground recursion case is
            // unaffected (it unfolds fully and returns a real verdict). (matches
            // the burndown "every check-sat emits a verdict" principle.)
            if message.contains("recursion depth limit") && command_contributes_to_problem(cmd) {
                eprintln_smt_error(message);
                transcript.mark_incomplete();
                return true;
            }
            if maybe_handle_recoverable_execution_error(transcript, cmd, &message) {
                // SOUNDNESS: the command was dropped after a recoverable
                // elaboration failure (e.g. an `assert` over an unknown symbol).
                // If it contributed to the problem, taint so check-sat answers
                // `unknown` rather than a wrong sat on the remaining assertions.
                if command_contributes_to_problem(cmd) {
                    transcript.mark_incomplete();
                }
                return true;
            }
            eprintln_smt_error(message);
            false
        }
    }
}

/// Compute the SMT-LIB output for `(get-interpolant A B)`.
///
/// Returns the interpolant as a rendered S-expression on success, or a
/// `(error "...")` message when the request falls outside the supported
/// fragment or no sound interpolant can be produced. Soundness first: a wrong
/// interpolant is never emitted — failures are surfaced as errors.
fn compute_interpolant_output(executor: &Executor, a: &Term, b: &Term) -> String {
    // Resolve declared symbol sorts from the elaboration context so the
    // candidate interpolant is validated in the right arithmetic theory.
    let ctx = executor.context();
    let resolver = |name: &str| -> Option<ay_chc::ChcSort> {
        ctx.symbol_sort(name)
            .map(|s| ay_chc::ChcSort::from(s.clone()))
    };

    match ay_chc::compute_smt_interpolant(a, b, &resolver) {
        Ok(interpolant) => interpolant.to_string(),
        Err(ay_chc::InterpolantError::Unsupported(msg)) => {
            format!("(error \"{}\")", escape_string_contents(&msg))
        }
    }
}

/// Generate human-readable explanation if `--explain` is active.
///
/// Called after all commands have been processed in non-interactive mode.
/// Uses the executor's last result to determine what to explain. On UNSAT,
/// the Phase 1 reason-code block (#8693) is also emitted: in `plain` format
/// it prepends to the existing English walk-through, in `json` format it
/// replaces the walk-through entirely (tooling consumers want a clean line).
fn maybe_explain(executor: &mut Executor) {
    if !EXPLAIN_ENABLED.load(std::sync::atomic::Ordering::Relaxed) {
        return;
    }
    let is_json = EXPLAIN_FORMAT_JSON.load(std::sync::atomic::Ordering::Relaxed);
    let is_unsat = executor.last_result_is_unsat();
    // Phase 1 reason-code block runs first on UNSAT. Unknown and SAT fall
    // through to the existing English explainer.
    if is_unsat {
        let format = if is_json {
            explain_reason::ExplainFormat::Json
        } else {
            explain_reason::ExplainFormat::Plain
        };
        explain_reason::emit_unsat_reason(executor, format);
        // JSON consumers want a single parseable line — skip the rich English
        // block, which is multi-line prose.
        if is_json {
            return;
        }
    }
    explain::explain_result(executor);
}

/// Render a recognized SAT solution if `--visualize` is active.
///
/// This issues an internal `(get-model)` query after the final `check-sat`.
/// The query is presentation-only and is not printed unless the formatter
/// recognizes a supported board-shaped model.
fn maybe_visualize(input: &str, executor: &mut Executor, format: Option<VisualizationFormat>) {
    let Some(format) = format else {
        return;
    };
    if executor.last_result_is_unsat() || executor.last_result_is_unknown() {
        return;
    }

    let Ok(Some(model)) = executor.execute(&Command::GetModel) else {
        return;
    };
    if model.trim_start().starts_with("(error") {
        return;
    }
    if let Some(rendered) = render_solution_visualization(input, &model, format) {
        safe_println!("{rendered}");
    }
}

const SMT_BV_BATCH_TEMPLATE_APPLICATION_COUNTER: &str = "smt_bv_batch_template_applications";
const SMT_LRA_BASIS_REGION_ARTIFACT: &str = "smt-lra-basis-regions";
const SMT_LRA_BASIS_REGION_APPLICATION_COUNTER: &str =
    "solver_program.lra_basis_region.batch_native_applies";
const SMT_LRA_BASIS_REGION_PROFILE_ENABLED_COUNTER: &str =
    "solver_program.profile.lra_basis_region.enabled";
const SMT_LRA_BASIS_REGION_BOUNDARY_CHECKS_COUNTER: &str =
    "solver_program.lra_basis_region.boundary_checks";
const SMT_LRA_BASIS_REGION_REQUESTS_QUEUED_COUNTER: &str =
    "solver_program.lra_basis_region.requests_queued";
const SMT_LRA_SPARSE_SUBSTITUTE_ARTIFACT: &str = "smt-lra-sparse-substitute";
const SMT_LRA_SPARSE_SUBSTITUTE_APPLICATION_COUNTER: &str =
    "lra_external_codegen_backend_substitute_native_applies";
const SMT_LRA_SPARSE_SUBSTITUTE_LEGACY_APPLICATION_COUNTER: &str =
    "lra_external_codegen_backend_substitute_applies";
const SMT_LRA_SPARSE_SUBSTITUTE_WRAPPER_COUNTER: &str =
    "lra_external_codegen_backend_substitute_wrapper_applies";
const SMT_LRA_SPARSE_SUBSTITUTE_NATIVE_EMPTY_TARGET_COUNTER: &str =
    "lra_external_codegen_backend_substitute_native_empty_target_applies";
const SMT_LRA_SPARSE_SUBSTITUTE_NATIVE_NON_EMPTY_TARGET_COUNTER: &str =
    "lra_external_codegen_backend_substitute_native_non_empty_target_applies";
const SMT_LRA_SPARSE_SUBSTITUTE_RUNTIME_COUNTER: &str =
    "lra_external_codegen_backend_substitute_runtime_applies";
const SMT_LRA_SPARSE_SUBSTITUTE_EVIDENCE_WAIT_ATTEMPTS_COUNTER: &str =
    "lra_external_codegen_backend_substitute_evidence_wait_attempts";
const SMT_LRA_SPARSE_SUBSTITUTE_EVIDENCE_WAIT_HITS_COUNTER: &str =
    "lra_external_codegen_backend_substitute_evidence_wait_hits";
const SMT_LRA_SPARSE_SUBSTITUTE_EVIDENCE_WAIT_TIMEOUTS_COUNTER: &str =
    "lra_external_codegen_backend_substitute_evidence_wait_timeouts";
const SMT_LRA_SPARSE_SUBSTITUTE_EVIDENCE_WAIT_POLLS_COUNTER: &str =
    "lra_external_codegen_backend_substitute_evidence_wait_polls";
const SMT_LRA_SPARSE_SUBSTITUTE_EVIDENCE_WAIT_US_TOTAL_COUNTER: &str =
    "lra_external_codegen_backend_substitute_evidence_wait_us_total";
const SMT_LRA_SPARSE_SUBSTITUTE_PROFILE_ENABLED_COUNTER: &str =
    "solver_program.profile.lra_sparse_substitute.enabled";
const SMT_NATIVE_CODE_HELPER_APPLICATION_COUNTER: &str = "smt_native_code_helper_applications";

fn insert_unsupported_smt_jit_application_counters(run_stats: &mut stats_output::RunStatistics) {
    run_stats.insert(SMT_BV_BATCH_TEMPLATE_APPLICATION_COUNTER, 0);
    run_stats.insert(SMT_NATIVE_CODE_HELPER_APPLICATION_COUNTER, 0);
}

fn trimmed_env_value(name: &str) -> Option<String> {
    std::env::var(name)
        .ok()
        .map(|value| value.trim().to_string())
        .filter(|value| !value.is_empty())
}

fn smt_competition_jit_candidate_mode() -> String {
    trimmed_env_value("AY_COMPETITION_JIT_CANDIDATE_MODE")
        .or_else(|| trimmed_env_value("AY_COMPETITION_JIT_MODE"))
        .unwrap_or_else(|| "solver-program".to_string())
}

fn attach_smt_lra_competition_jit_for_artifact(
    run_stats: &mut stats_output::RunStatistics,
    artifact_id: &str,
    candidate_mode: &str,
) {
    let application_counter = match artifact_id {
        SMT_LRA_BASIS_REGION_ARTIFACT => {
            if run_stats
                .counters
                .get(SMT_LRA_BASIS_REGION_PROFILE_ENABLED_COUNTER)
                .copied()
                != Some(1)
            {
                return;
            }
            // #9601: promotion is gated on actual native batch substitute
            // applications; boundary/request counters remain telemetry.
            SMT_LRA_BASIS_REGION_APPLICATION_COUNTER
        }
        SMT_LRA_SPARSE_SUBSTITUTE_ARTIFACT => {
            if !run_stats
                .counters
                .contains_key(SMT_LRA_SPARSE_SUBSTITUTE_PROFILE_ENABLED_COUNTER)
                && !run_stats
                    .counters
                    .contains_key(SMT_LRA_SPARSE_SUBSTITUTE_APPLICATION_COUNTER)
            {
                return;
            }
            SMT_LRA_SPARSE_SUBSTITUTE_APPLICATION_COUNTER
        }
        _ => return,
    };

    let application_count = run_stats
        .counters
        .get(application_counter)
        .copied()
        .unwrap_or(0);
    run_stats.competition_jit = Some(stats_output::CompetitionJitEvidence {
        track: "smt".to_string(),
        artifact_id: artifact_id.to_string(),
        candidate_mode: candidate_mode.to_string(),
        application_counter: Some(stats_output::CompetitionJitApplicationCounter {
            key: application_counter.to_string(),
            value: application_count,
        }),
    });
}

fn attach_smt_lra_competition_jit(run_stats: &mut stats_output::RunStatistics) {
    let requested_artifact = trimmed_env_value("AY_COMPETITION_JIT_ARTIFACT")
        .unwrap_or_else(|| SMT_LRA_BASIS_REGION_ARTIFACT.to_string());
    let candidate_mode = smt_competition_jit_candidate_mode();
    attach_smt_lra_competition_jit_for_artifact(
        run_stats,
        requested_artifact.as_str(),
        candidate_mode.as_str(),
    );
}

/// Print SMT-LIB executor statistics to stderr (Z3 `-st` style)
/// plus the canonical RunStatistics envelope.
fn print_smt_stats(
    executor: &Executor,
    formula_stats: Option<&FormulaStats>,
    stats_cfg: stats_output::StatsConfig,
) {
    if stats_cfg.human {
        let dpll_stats = executor.statistics();
        safe_eprintln!("{dpll_stats}");
        if let Some(formula_stats) = formula_stats {
            safe_eprintln!("{formula_stats}");
        }
    }

    // Canonical envelope
    let dpll_stats = executor.statistics();
    let elapsed = super::global_elapsed();
    let result_str = if executor.last_result_is_unsat() {
        "unsat"
    } else if executor.last_result_is_unknown() {
        "unknown"
    } else {
        "sat"
    };
    let mut run_stats =
        stats_output::RunStatistics::new(stats_output::SolveMode::Smt, result_str, elapsed);
    run_stats.insert("conflicts", dpll_stats.conflicts);
    run_stats.insert("decisions", dpll_stats.decisions);
    run_stats.insert("propagations", dpll_stats.propagations);
    run_stats.insert("restarts", dpll_stats.restarts);
    run_stats.insert("smt.theory_conflicts", dpll_stats.theory_conflicts);
    run_stats.insert("smt.theory_propagations", dpll_stats.theory_propagations);
    // #8153: Proof/explainability stats
    if dpll_stats.proof_clause_count > 0 {
        run_stats.insert("smt.proof_clause_count", dpll_stats.proof_clause_count);
        run_stats.insert("smt.proof_complete", u64::from(dpll_stats.proof_complete));
    }
    if dpll_stats.annotated_core_entries > 0 {
        run_stats.insert(
            "smt.annotated_core_entries",
            dpll_stats.annotated_core_entries,
        );
        run_stats.insert(
            "smt.annotated_core_theories",
            dpll_stats.annotated_core_theories,
        );
    }
    // #8640: Resource consumption statistics.
    run_stats.insert(
        "resource.rss_peak_bytes",
        ay_sys::current_rss_bytes() as u64,
    );
    run_stats.insert(
        "resource.memory_limit_bytes",
        ay_sys::get_process_memory_limit() as u64,
    );
    run_stats.insert("resource.term_bytes", dpll_stats.term_bytes);
    run_stats.insert("resource.term_count", dpll_stats.term_count);
    run_stats.insert("resource.learned_clauses", dpll_stats.learned_clauses);
    if dpll_stats.refinement_count > 0 {
        run_stats.insert("resource.refinement_count", dpll_stats.refinement_count);
    }
    run_stats.insert("time.total_ms", elapsed.as_millis() as u64);

    // #8165: Theory solver observability counters from extra stats
    for key in [
        "smt.no_rounds",
        "smt.unknown_returns",
        "smt.diseq_propagations",
        "smt.conflicts.lia",
        "smt.conflicts.lra",
        "smt.conflicts.euf",
        "smt.conflicts.arrays",
        "smt.checks.lia",
        "smt.checks.lra",
        "smt.checks.euf",
        "smt.checks.arrays",
        "arrays_candidate_pairs_calls",
        "arrays_candidate_pairs_generated",
        "arrays_candidate_pairs_memo_hits",
        "smt.props.lia",
        "smt.props.lra",
        "smt.props.euf",
        "smt.partial_clauses",
        "model_validation.checked",
        "model_validation.delegated",
        "model_validation.array_delegated",
        "model_validation.sat_fallback",
        "model_validation.total",
        "lra_external_codegen_backend_substitute_compile_attempts",
        "lra_external_codegen_backend_substitute_compilations",
        "lra_external_codegen_backend_substitute_compile_failures",
        "lra_external_codegen_backend_substitute_backoff_skips",
        "lra_external_codegen_backend_substitute_disabled_skips",
        "lra_external_codegen_backend_substitute_applies",
        "lra_external_codegen_backend_substitute_wrapper_applies",
        "lra_external_codegen_backend_substitute_native_applies",
        "lra_external_codegen_backend_substitute_native_empty_target_applies",
        "lra_external_codegen_backend_substitute_native_non_empty_target_applies",
        "lra_external_codegen_backend_substitute_runtime_applies",
        "lra_external_codegen_backend_substitute_fallback_applies",
        "lra_external_codegen_backend_substitute_overflow_fallbacks",
        "lra_external_codegen_backend_substitute_queue_submissions",
        "lra_external_codegen_backend_substitute_queue_installs",
        "lra_external_codegen_backend_substitute_queue_budget_rejects",
        "lra_external_codegen_backend_substitute_queue_dropped_stale",
        "lra_external_codegen_backend_substitute_queue_compile_us_total",
        "lra_external_codegen_backend_substitute_queue_compile_us_max",
        "lra_external_codegen_backend_substitute_queue_submit_to_install_us_total",
        "lra_external_codegen_backend_substitute_queue_submit_to_install_us_max",
        "lra_external_codegen_backend_substitute_evidence_wait_attempts",
        "lra_external_codegen_backend_substitute_evidence_wait_hits",
        "lra_external_codegen_backend_substitute_evidence_wait_timeouts",
        "lra_external_codegen_backend_substitute_evidence_wait_polls",
        "lra_external_codegen_backend_substitute_evidence_wait_us_total",
    ] {
        if let Some(v) = dpll_stats.get_int(key) {
            if v > 0 {
                run_stats.insert(key, v);
            }
        }
    }
    for (key, value) in &dpll_stats.extra {
        if !key.starts_with("solver_program.") {
            continue;
        }
        let ay_dpll::StatValue::Int(value) = value else {
            continue;
        };
        if *value > 0
            || key == "solver_program.schema_version"
            || key.starts_with("solver_program.profile.")
            || key == SMT_LRA_BASIS_REGION_APPLICATION_COUNTER
            || key == SMT_LRA_BASIS_REGION_BOUNDARY_CHECKS_COUNTER
            || key == SMT_LRA_BASIS_REGION_REQUESTS_QUEUED_COUNTER
        {
            run_stats.insert(key, *value);
        }
    }
    if trimmed_env_value("AY_COMPETITION_JIT_ARTIFACT").as_deref()
        == Some(SMT_LRA_SPARSE_SUBSTITUTE_ARTIFACT)
    {
        let applies = dpll_stats
            .get_int(SMT_LRA_SPARSE_SUBSTITUTE_APPLICATION_COUNTER)
            .unwrap_or(0);
        run_stats.insert(SMT_LRA_SPARSE_SUBSTITUTE_APPLICATION_COUNTER, applies);
        let legacy_applies = dpll_stats
            .get_int(SMT_LRA_SPARSE_SUBSTITUTE_LEGACY_APPLICATION_COUNTER)
            .unwrap_or(applies);
        run_stats.insert(
            SMT_LRA_SPARSE_SUBSTITUTE_LEGACY_APPLICATION_COUNTER,
            legacy_applies,
        );
        let wrapper_applies = dpll_stats
            .get_int(SMT_LRA_SPARSE_SUBSTITUTE_WRAPPER_COUNTER)
            .unwrap_or(0);
        run_stats.insert(SMT_LRA_SPARSE_SUBSTITUTE_WRAPPER_COUNTER, wrapper_applies);
        let native_empty_target_applies = dpll_stats
            .get_int(SMT_LRA_SPARSE_SUBSTITUTE_NATIVE_EMPTY_TARGET_COUNTER)
            .unwrap_or(0);
        run_stats.insert(
            SMT_LRA_SPARSE_SUBSTITUTE_NATIVE_EMPTY_TARGET_COUNTER,
            native_empty_target_applies,
        );
        let native_non_empty_target_applies = dpll_stats
            .get_int(SMT_LRA_SPARSE_SUBSTITUTE_NATIVE_NON_EMPTY_TARGET_COUNTER)
            .unwrap_or(0);
        run_stats.insert(
            SMT_LRA_SPARSE_SUBSTITUTE_NATIVE_NON_EMPTY_TARGET_COUNTER,
            native_non_empty_target_applies,
        );
        let runtime_applies = dpll_stats
            .get_int(SMT_LRA_SPARSE_SUBSTITUTE_RUNTIME_COUNTER)
            .unwrap_or(0);
        run_stats.insert(SMT_LRA_SPARSE_SUBSTITUTE_RUNTIME_COUNTER, runtime_applies);
        for wait_counter in [
            SMT_LRA_SPARSE_SUBSTITUTE_EVIDENCE_WAIT_ATTEMPTS_COUNTER,
            SMT_LRA_SPARSE_SUBSTITUTE_EVIDENCE_WAIT_HITS_COUNTER,
            SMT_LRA_SPARSE_SUBSTITUTE_EVIDENCE_WAIT_TIMEOUTS_COUNTER,
            SMT_LRA_SPARSE_SUBSTITUTE_EVIDENCE_WAIT_POLLS_COUNTER,
            SMT_LRA_SPARSE_SUBSTITUTE_EVIDENCE_WAIT_US_TOTAL_COUNTER,
        ] {
            let value = dpll_stats.get_int(wait_counter).unwrap_or(0);
            run_stats.insert(wait_counter, value);
        }
    }
    insert_unsupported_smt_jit_application_counters(&mut run_stats);
    attach_smt_lra_competition_jit(&mut run_stats);
    run_stats.emit(stats_cfg);
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Duration;

    /// Feed `input` to `IncrementalDepth` one physical line at a time (mirroring
    /// the `read_line` accumulation) and return the final depth.
    fn scan_depth_by_line(input: &str) -> IncrementalDepth {
        let mut d = IncrementalDepth::default();
        for line in input.split_inclusive('\n') {
            d.feed(line);
        }
        d
    }

    #[test]
    fn incremental_depth_balances_single_line_command() {
        assert_eq!(scan_depth_by_line("(check-sat)\n").depth, 0);
        assert_eq!(scan_depth_by_line("(assert (= x 1))\n").depth, 0);
    }

    #[test]
    fn incremental_depth_open_until_closed_across_lines() {
        // A multi-line command is only "complete" (depth 0) on the closing line.
        let mut d = IncrementalDepth::default();
        d.feed("(assert (or\n");
        assert!(d.depth > 0, "mid-command depth must stay positive");
        d.feed("  (= x 1)\n");
        assert!(d.depth > 0);
        d.feed("  (= y 2)))\n");
        assert_eq!(d.depth, 0, "closing line returns to depth 0");
    }

    #[test]
    fn incremental_depth_ignores_parens_in_line_comment() {
        // A ')' inside a `;` comment must not close a real group.
        assert_eq!(scan_depth_by_line("(echo x) ; )))(((\n").depth, 0);
        let mut d = IncrementalDepth::default();
        d.feed("(assert true ; ) ) )\n");
        assert_eq!(d.depth, 1, "comment parens are inert");
    }

    #[test]
    fn incremental_depth_ignores_parens_in_string_and_pipe() {
        // Parens inside a "..." string literal or |...| quoted symbol are inert,
        // including when the literal spans multiple physical lines.
        assert_eq!(scan_depth_by_line("(echo \"(((\")\n").depth, 0);
        assert_eq!(scan_depth_by_line("(echo \"a\"\"b)\")\n").depth, 0);
        // Multi-line quoted symbol (as in `(set-info :source | ... |)`).
        let mut d = IncrementalDepth::default();
        d.feed("(set-info :source |\n");
        assert_eq!(d.depth, 1);
        d.feed("  text with ) ( parens and no effect\n");
        assert_eq!(d.depth, 1, "still inside quoted symbol");
        d.feed("|)\n");
        assert_eq!(d.depth, 0, "closing | then ) balances");
    }

    #[test]
    fn incremental_depth_matches_naive_paren_count_outside_literals() {
        // On the benchmark shape (no strings/pipes mid-command), the tracker's
        // depth equals the naive open-minus-close count the old gate used.
        for s in [
            "(a (b) (c (d)))\n",
            "(assert (<= (+ x y) 3))\n",
            "(push 1)\n(assert x)\n",
        ] {
            let naive = s.matches('(').count() as i64 - s.matches(')').count() as i64;
            assert_eq!(scan_depth_by_line(s).depth, naive, "input: {s:?}");
        }
    }

    #[test]
    fn dedicated_subcommand_redirect_covers_known_non_smt_extensions() {
        // Every extension `looks_like_input_path_arg` (main.rs) classifies as
        // a solver input but `ay solve` cannot parse gets a redirect message.
        for (path, needle) in [
            ("model.fzn", "ay flatzinc solve"),
            ("Model.QDIMACS", "ay qbf solve"),
            ("inst.wcnf", "ay maxsat solve"),
            ("inst.wcnf.xz", "ay maxsat solve"),
            ("inst.opb", "ay pb solve"),
            ("prob.mps", "ay lp solve"),
            ("prob.lp", "ay lp solve"),
            ("circuit.aig", "not supported"),
            ("circuit.aag", "not supported"),
            ("synth.sl", "not supported"),
        ] {
            let msg = dedicated_subcommand_redirect(path)
                .unwrap_or_else(|| panic!("{path} should be redirected"));
            assert!(msg.contains(needle), "{path}: {msg} missing {needle}");
        }

        // SMT-LIB / DIMACS / CHC inputs proceed through normal routing.
        for path in ["input.smt2", "input.cnf", "input.dimacs", "input.smt"] {
            assert_eq!(dedicated_subcommand_redirect(path), None, "{path}");
        }
    }

    #[test]
    fn reason_unknown_inner_extracts_unquoted_token() {
        // AY prints the reason UNQUOTED; the token may contain spaces/parens.
        assert_eq!(
            reason_unknown_inner("(:reason-unknown timeout)"),
            Some("timeout")
        );
        assert_eq!(
            reason_unknown_inner("(:reason-unknown (incomplete quantifier-unhandled))"),
            Some("(incomplete quantifier-unhandled)")
        );
        // Not a reason-unknown line -> untouched.
        assert_eq!(reason_unknown_inner("(:status unknown)"), None);
    }

    #[test]
    fn z3_reason_unknown_maps_resource_family_to_canceled() {
        // Verus's `reason_unknown_canceled_str()` is exactly this line.
        for r in ["timeout", "resourceout", "memout", "interrupted"] {
            assert_eq!(
                z3_reason_unknown_output(r),
                "(:reason-unknown \"canceled\")",
                "{r} should map to Z3 canceled"
            );
        }
    }

    #[test]
    fn z3_reason_unknown_keeps_z3_unknown_verbatim() {
        // Z3's own "unknown" reason; Verus matches it literally.
        assert_eq!(
            z3_reason_unknown_output("unknown"),
            "(:reason-unknown \"unknown\")"
        );
    }

    #[test]
    fn z3_reason_unknown_incompleteness_matches_verus_incomplete_prefix() {
        // Verus routes any `(:reason-unknown "(incomplete...` to Incomplete
        // (goal NOT proved). Every incompleteness form must carry that prefix.
        let incomplete_prefix = "(:reason-unknown \"(incomplete";
        for r in [
            "incomplete",
            "unsupported",
            "(unsupported arithmetic)",
            "(unsupported mixed-collection)",
            "internal-error",
            "(incomplete quantifier-unhandled)",
            "(incomplete proof-trusted)",
            "some-future-reason-code",
        ] {
            let out = z3_reason_unknown_output(r);
            assert!(
                out.starts_with(incomplete_prefix),
                "reason {r:?} produced {out:?}, which is neither canceled/unknown \
                 nor an (incomplete ...) form Verus accepts"
            );
        }
    }

    #[test]
    fn z3_reason_unknown_preserves_already_incomplete_forms() {
        // Quantifier detail is preserved verbatim (already Z3-shaped).
        assert_eq!(
            z3_reason_unknown_output("(incomplete quantifier-unhandled)"),
            "(:reason-unknown \"(incomplete quantifier-unhandled)\")"
        );
    }

    #[test]
    fn smt_lra_competition_jit_uses_batch_native_applies_not_boundary_or_requests() {
        let mut run_stats =
            stats_output::RunStatistics::new(stats_output::SolveMode::Smt, "sat", Duration::ZERO);
        run_stats.insert(SMT_LRA_BASIS_REGION_PROFILE_ENABLED_COUNTER, 1);
        run_stats.insert(SMT_LRA_BASIS_REGION_APPLICATION_COUNTER, 3);
        run_stats.insert(SMT_LRA_BASIS_REGION_BOUNDARY_CHECKS_COUNTER, 4);
        run_stats.insert(SMT_LRA_BASIS_REGION_REQUESTS_QUEUED_COUNTER, 7);

        attach_smt_lra_competition_jit_for_artifact(
            &mut run_stats,
            SMT_LRA_BASIS_REGION_ARTIFACT,
            "solver-program",
        );

        let evidence = run_stats
            .competition_jit
            .expect("enabled LRA basis-region profile should attach SMT competition evidence");
        let application_counter = evidence
            .application_counter
            .expect("SMT LRA competition evidence should include an application counter");
        assert_eq!(evidence.track, "smt");
        assert_eq!(evidence.artifact_id, SMT_LRA_BASIS_REGION_ARTIFACT);
        assert_eq!(evidence.candidate_mode, "solver-program");
        assert_eq!(
            application_counter.key,
            SMT_LRA_BASIS_REGION_APPLICATION_COUNTER
        );
        assert_eq!(application_counter.value, 3);
        assert_eq!(
            run_stats
                .counters
                .get(SMT_LRA_BASIS_REGION_BOUNDARY_CHECKS_COUNTER)
                .copied(),
            Some(4)
        );
        assert_eq!(
            run_stats
                .counters
                .get(SMT_LRA_BASIS_REGION_REQUESTS_QUEUED_COUNTER)
                .copied(),
            Some(7)
        );
    }

    #[test]
    fn smt_lra_competition_jit_can_use_sparse_substitute_applies() {
        let mut run_stats =
            stats_output::RunStatistics::new(stats_output::SolveMode::Smt, "sat", Duration::ZERO);
        run_stats.insert(SMT_LRA_SPARSE_SUBSTITUTE_PROFILE_ENABLED_COUNTER, 1);
        run_stats.insert(SMT_LRA_SPARSE_SUBSTITUTE_APPLICATION_COUNTER, 0);

        attach_smt_lra_competition_jit_for_artifact(
            &mut run_stats,
            SMT_LRA_SPARSE_SUBSTITUTE_ARTIFACT,
            "solver-program",
        );

        let evidence = run_stats
            .competition_jit
            .expect("requested sparse-substitute profile should attach SMT competition evidence");
        let application_counter = evidence
            .application_counter
            .expect("SMT sparse-substitute evidence should include an application counter");
        assert_eq!(evidence.track, "smt");
        assert_eq!(evidence.artifact_id, SMT_LRA_SPARSE_SUBSTITUTE_ARTIFACT);
        assert_eq!(evidence.candidate_mode, "solver-program");
        assert_eq!(
            application_counter.key,
            SMT_LRA_SPARSE_SUBSTITUTE_APPLICATION_COUNTER
        );
        assert_eq!(application_counter.value, 0);
    }
}

/// Write verified-firewall Lean proofs to the `--emit-firewall-lean` directory,
/// one file per groundable theory lemma in the last proof. Each file imports the
/// verified `AySoundness` theorems and kernel-checks independently. No-op unless
/// the flag was given and a proof is available.
fn maybe_emit_firewall_lean(executor: &Executor) {
    let Some(dir) = crate::FIREWALL_LEAN_DIR.get() else {
        return;
    };
    let Some(proof) = executor.last_proof() else {
        return;
    };
    let leans = executor.emit_datatype_firewall_lean(proof);
    if leans.is_empty() {
        return;
    }
    if let Err(e) = std::fs::create_dir_all(dir) {
        safe_eprintln!(
            "Error: failed to create firewall-lean directory {}: {e}",
            dir.display()
        );
        return;
    }
    for (i, lean) in leans.iter().enumerate() {
        let path = dir.join(format!("firewall_{i}.lean"));
        if let Err(e) = std::fs::write(&path, lean) {
            safe_eprintln!(
                "Error: failed to write firewall Lean {}: {e}",
                path.display()
            );
        }
    }
    if !crate::quiet_enabled() {
        // Proof-write announcement is stderr commentary; the proof files above
        // are written regardless of `-q`/`--quiet`.
        safe_eprintln!(
            "ay: wrote {} verified-firewall Lean proof(s) to {}",
            leans.len(),
            dir.display()
        );
    }
}

fn write_alethe_proof(
    executor: &Executor,
    proof_config: &ProofConfig,
    problem: ProofArtifactProblem<'_>,
    theory: ProofArtifactTheoryMetadata,
) {
    if proof_config.format != ProofFormat::Alethe {
        safe_eprintln!(
            "Error: proof file '{}' uses DRAT/LRAT/Lean4 format, but SMT-LIB solving produces Alethe proofs",
            proof_config.path
        );
        std::process::exit(1);
    }
    if !executor.last_result_is_unsat() {
        return;
    }
    // Verified-firewall Lean emission (`--emit-firewall-lean`). Independent of
    // the trust-fallback suppression below: each emitted file reconstructs and
    // kernel-verifies a specific groundable theory lemma, so it is valid even
    // when the overall Alethe proof still rides a trust step elsewhere.
    maybe_emit_firewall_lean(executor);
    // #8759: In strict-proof mode, suppress proof file writing when the
    // terminal derivation rides on a trust fallback. The CLI has already
    // printed `unknown` + `(:reason-unknown (incomplete proof-trusted))`;
    // emitting a trust-tainted "UNSAT proof" would contradict that verdict.
    if strict_proofs_enabled() && terminal_trust_detected(executor) {
        return;
    }
    // #8821: Use the fallible API so printer errors (e.g., missing Farkas
    // annotation for la_generic / lia_generic steps) abort with a non-zero
    // exit status instead of silently writing an `(error ...)` document
    // that a user might mistake for a legitimate proof file.
    //
    // Use the same problem-scoped path as `(get-proof)`: symbols declared by
    // the SMT-LIB problem belong in the problem file, not in the Alethe proof
    // stream that Carcara checks against that problem.
    //
    // Failure posture depends on provenance: an explicit `--proof FILE` fails
    // loud (exit 1) if AY cannot render a checkable certificate. A *synthesized
    // default* certificate (proof-carrying-on-by-default, no explicit `--proof`)
    // must NOT fail the run — the UNSAT verdict is unchanged; only the optional
    // certificate is missing — so it warns and continues.
    let is_default = proof_config.synthesized_default;
    // #rss-vs-z3: STREAM the certificate to disk instead of materializing it
    // as one in-memory String. Large default-mode certificates (pgm_protocol.4
    // renders 785MB of Alethe) transiently held ~1.5x their size in RAM during
    // String growth — the dominant share of a 1.4GB peak RSS on a 60MB solve.
    // The byte stream is identical to the previous `String` + `fs::write`
    // path. Render into a temp file in the target directory and rename on
    // success so failure modes match the old semantics exactly: no partial
    // certificate ever appears at the target path, and a pre-existing file
    // there is left untouched on failure.
    if executor.last_proof().is_none() {
        if is_default {
            safe_eprintln!(
                "c warning: no proof certificate emitted (UNSAT produced no reconstructable proof); pass --strict-proofs to require one"
            );
            return;
        }
        safe_eprintln!(
            "Error: UNSAT result produced no proof despite --proof {}",
            proof_config.path
        );
        std::process::exit(1);
    }
    let temp_path = format!("{}.tmp-{}", proof_config.path, std::process::id());
    let stream_result = match std::fs::File::create(&temp_path) {
        Ok(file) => {
            let mut writer = std::io::BufWriter::with_capacity(1 << 20, file);
            let render = executor.try_export_last_proof_alethe_for_problem_scope_to(&mut writer);
            match render {
                Some(Ok(())) => {
                    use std::io::Write as _;
                    writer
                        .flush()
                        .map_err(ay_proof::AletheStreamError::Io)
                        .and_then(|()| {
                            std::fs::rename(&temp_path, &proof_config.path)
                                .map_err(ay_proof::AletheStreamError::Io)
                        })
                }
                Some(Err(error)) => {
                    drop(writer);
                    let _ = std::fs::remove_file(&temp_path);
                    Err(error)
                }
                None => unreachable!("last_proof presence checked above"),
            }
        }
        Err(error) => Err(ay_proof::AletheStreamError::Io(error)),
    };
    match stream_result {
        Ok(()) => {}
        Err(ay_proof::AletheStreamError::Print(error)) => {
            if is_default {
                safe_eprintln!(
                    "c warning: no proof certificate emitted (proof not fully checkable: {error}); pass --strict-proofs to require one"
                );
                return;
            }
            safe_eprintln!(
                "Error: refusing to write unverifiable proof to {} (#8821): {error}",
                proof_config.path
            );
            std::process::exit(1);
        }
        Err(ay_proof::AletheStreamError::Io(error)) => {
            let _ = std::fs::remove_file(&temp_path);
            if is_default {
                // A synthesized-default certificate is optional and AY-specific (z3
                // writes no proof by default). A write failure — most commonly a
                // read-only input directory (nix store, docker RO mount, CI cache,
                // mounted corpus) — must NOT change the exit code: the UNSAT verdict
                // is already on stdout and is unaffected. Warn and continue, exactly
                // as the render-failure branches above do for the default case.
                // (Previously this exited 1 with a correct `unsat` on stdout, which
                // broke every read-only deployment.)
                safe_eprintln!(
                    "c warning: could not write default proof file {} ({error}); UNSAT verdict is unaffected",
                    proof_config.path
                );
                return;
            }
            safe_eprintln!(
                "Error: failed to write proof file {}: {error}",
                proof_config.path
            );
            std::process::exit(1);
        }
    }
    write_proof_artifact_or_exit(problem, proof_config, theory);
}

const DIMACS_STDIN_SNIFF_LIMIT: usize = 64 * 1024;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum DimacsPrefixKind {
    Dimacs,
    NotDimacs,
    NeedMore,
}

fn trim_ascii(mut bytes: &[u8]) -> &[u8] {
    while bytes
        .first()
        .is_some_and(|b| matches!(b, b' ' | b'\t' | b'\r' | b'\n'))
    {
        bytes = &bytes[1..];
    }
    while bytes
        .last()
        .is_some_and(|b| matches!(b, b' ' | b'\t' | b'\r' | b'\n'))
    {
        bytes = &bytes[..bytes.len() - 1];
    }
    bytes
}

fn classify_dimacs_prefix(prefix: &[u8], eof: bool) -> DimacsPrefixKind {
    let mut line_start = 0;
    while line_start < prefix.len() {
        let mut line_end = line_start;
        while line_end < prefix.len() && prefix[line_end] != b'\n' {
            line_end += 1;
        }
        if line_end == prefix.len() && !eof {
            return DimacsPrefixKind::NeedMore;
        }

        let line = trim_ascii(&prefix[line_start..line_end]);
        if line.is_empty() || line.starts_with(b"c") {
            line_start = line_end.saturating_add(1);
            continue;
        }
        if line.starts_with(b"p cnf") {
            return DimacsPrefixKind::Dimacs;
        }
        return DimacsPrefixKind::NotDimacs;
    }

    if eof {
        DimacsPrefixKind::NotDimacs
    } else {
        DimacsPrefixKind::NeedMore
    }
}

fn read_piped_input_or_stream_dimacs<R>(
    mut reader: R,
    stats_cfg: stats_output::StatsConfig,
    proof_config: Option<&ProofConfig>,
) -> io::Result<Option<String>>
where
    R: Read,
{
    if let Some(proof) =
        proof_config.filter(|_| !VERIFY_PROOF_ENABLED.load(std::sync::atomic::Ordering::SeqCst))
    {
        let mut prefix = Vec::new();
        let mut eof = false;

        loop {
            match classify_dimacs_prefix(&prefix, eof) {
                DimacsPrefixKind::Dimacs => {
                    reject_bv_cnf_export_for_non_smt_route("DIMACS stdin");
                    let replay = io::Cursor::new(prefix).chain(reader);
                    dimacs::run_dimacs_proof_from_reader(replay, stats_cfg, proof);
                    return Ok(None);
                }
                DimacsPrefixKind::NotDimacs => break,
                DimacsPrefixKind::NeedMore => {}
            }

            if eof || prefix.len() >= DIMACS_STDIN_SNIFF_LIMIT {
                break;
            }

            let mut buf = [0u8; 8192];
            let limit = (DIMACS_STDIN_SNIFF_LIMIT - prefix.len()).min(buf.len());
            let read = reader.read(&mut buf[..limit])?;
            if read == 0 {
                eof = true;
            } else {
                prefix.extend_from_slice(&buf[..read]);
            }
        }

        let mut bytes = prefix;
        reader.read_to_end(&mut bytes)?;
        return String::from_utf8(bytes)
            .map(Some)
            .map_err(|error| io::Error::new(io::ErrorKind::InvalidData, error));
    }

    let mut content = String::new();
    reader.read_to_string(&mut content)?;
    Ok(Some(content))
}

fn reject_bv_cnf_export_for_non_smt_route(route: &str) {
    if ay_core::trace_config().dump_bv_cnf_path.is_none() {
        return;
    }
    if let Err(error) = Executor::invalidate_bv_cnf_export_for_rejected_check() {
        eprintln_smt_error(error.to_string());
    } else {
        eprintln_smt_error(format!(
            "artifact export failed: --dump-bv-cnf supports only SMT-LIB pure QF_BV checks, not the {route} route"
        ));
    }
    std::process::exit(1);
}

/// Incremental, lexing-aware paren-depth tracker for the line-by-line stdin
/// reader (#inc-lra-parse).
///
/// The line-by-line loop accumulates physical lines into a buffer and must
/// decide when the buffer holds one or more *complete* top-level commands
/// before it hands the buffer to the (O(buffer)) `parse`. The historical gate
/// re-scanned the entire buffer every line (via `parse` + a naive
/// `matches('(')` count), which is O(command_lines × command_bytes) — quadratic
/// on the giant multi-line asserts emitted by BMC k-unrolling (a single assert
/// can span thousands of lines), and the dominant cost on incremental QF_LRA.
///
/// This tracker maintains the running SMT-LIB paren depth by scanning only each
/// *newly appended* line, correctly skipping `;` line comments, `"…"` string
/// literals (with `""` escape), and `|…|` quoted symbols — all of which may
/// carry an unbalanced paren and the latter two of which may span lines. When
/// the depth is `> 0` the command is provably incomplete, so the loop keeps
/// reading without touching `parse`, turning the accumulation into O(bytes).
///
/// Soundness: this only decides *when* to attempt a parse — never the parse
/// result. When the depth reaches `<= 0` the existing `parse` + naive-paren
/// recovery runs exactly as before, so a mis-tracked depth can at worst trigger
/// a parse that then self-heals through the unchanged error path. Gated by
/// `AY_INC_LINEAR_PARSE` (default on; set to `0`/`off` to restore the
/// parse-every-line behavior).
#[derive(Default)]
struct IncrementalDepth {
    depth: i64,
    in_string: bool,
    in_pipe: bool,
}

impl IncrementalDepth {
    /// Fold one freshly read physical line (including any trailing newline)
    /// into the running paren depth.
    fn feed(&mut self, line: &str) {
        let b = line.as_bytes();
        let mut i = 0;
        while i < b.len() {
            let c = b[i];
            if self.in_string {
                if c == b'"' {
                    // `""` inside a string literal is an escaped quote: stay in.
                    if i + 1 < b.len() && b[i + 1] == b'"' {
                        i += 2;
                        continue;
                    }
                    self.in_string = false;
                }
                i += 1;
                continue;
            }
            if self.in_pipe {
                if c == b'|' {
                    self.in_pipe = false;
                }
                i += 1;
                continue;
            }
            match c {
                // Line comment: the rest of this physical line is inert.
                b';' => break,
                b'"' => self.in_string = true,
                b'|' => self.in_pipe = true,
                b'(' => self.depth += 1,
                b')' => self.depth -= 1,
                _ => {}
            }
            i += 1;
        }
    }
}

pub(super) fn run_interactive(
    stats_cfg: stats_output::StatsConfig,
    proof_config: Option<&ProofConfig>,
    incremental: bool,
    visualization: Option<VisualizationFormat>,
    verbose: bool,
    validate: bool,
) {
    use std::io::IsTerminal;

    let stdin = io::stdin();
    let is_tty = stdin.is_terminal();

    // If stdin is piped (not a TTY) and not in incremental mode:
    //  - SMT-LIB is STREAMED command-by-command (like z3's `-in`), so a
    //    coprocess driver that holds stdin open sees each verdict and is not
    //    deadlocked by a read-to-EOF.
    //  - DIMACS and CHC are batch formats (whole content, never coprocess-driven)
    //    and keep the buffered path.
    // `--incremental` always uses the line-by-line path (#5360).
    if !is_tty && !incremental {
        let mut locked = stdin.lock();
        // Classify from a bounded prefix WITHOUT draining the stream. The sniff
        // reads only until the format is decided; a coprocess sends a full
        // command batch up front, so this does not block on input the peer is
        // withholding until it gets our reply. `classify_dimacs_prefix` returns
        // NotDimacs as soon as it sees the first `(` command line, so an SMT
        // coprocess is classified from its very first write.
        let mut prefix = Vec::new();
        let mut eof = false;
        while !eof
            && prefix.len() < DIMACS_STDIN_SNIFF_LIMIT
            && classify_dimacs_prefix(&prefix, eof) == DimacsPrefixKind::NeedMore
        {
            let mut buf = [0u8; 8192];
            let want = (DIMACS_STDIN_SNIFF_LIMIT - prefix.len()).min(buf.len());
            match locked.read(&mut buf[..want]) {
                Ok(0) => eof = true,
                Ok(read) => prefix.extend_from_slice(&buf[..read]),
                Err(e) => {
                    eprintln_smt_error(format_args!("Error reading stdin: {e}"));
                    std::process::exit(1);
                }
            }
        }

        let is_dimacs = classify_dimacs_prefix(&prefix, true) == DimacsPrefixKind::Dimacs;
        // CHC / fixedpoint are SMT-syntax but batch: their markers (`set-logic
        // HORN`, `declare-rel`/`rule`/`query`) appear in the first command or two,
        // well inside the sniff window.
        let is_chc_family = !is_dimacs && {
            let prefix_str = String::from_utf8_lossy(&prefix);
            is_horn_logic(&prefix_str) || is_fixedpoint_format(&prefix_str)
        };

        if !is_dimacs && !is_chc_family {
            // SMT-LIB: stream. Chain the sniffed prefix back in front of the live
            // stream so no byte is lost.
            let reader = io::BufReader::new(io::Cursor::new(prefix).chain(locked));
            run_interactive_smt_stream(reader, false, stats_cfg, proof_config, visualization);
            return;
        }

        // Batch (DIMACS / CHC): the existing buffered dispatch, now fed the
        // sniffed prefix followed by the rest of the stream.
        let combined = io::Cursor::new(prefix).chain(locked);
        let content = match read_piped_input_or_stream_dimacs(combined, stats_cfg, proof_config) {
            Ok(Some(content)) => content,
            Ok(None) => return,
            Err(e) => {
                eprintln_smt_error(format_args!("Error reading stdin: {e}"));
                std::process::exit(1);
            }
        };

        // Check for DIMACS CNF format (content-based detection for stdin)
        if dimacs::is_dimacs_format(&content) {
            reject_bv_cnf_export_for_non_smt_route("DIMACS stdin");
            dimacs::run_dimacs_from_content(&content, stats_cfg, proof_config);
            return;
        }

        // Check for HORN logic
        if is_horn_logic(&content) {
            reject_bv_cnf_export_for_non_smt_route("CHC stdin");
            chc_runner::run_chc_from_content(&content, verbose, validate, stats_cfg, proof_config);
            return;
        }

        // Check for Z3 fixedpoint (declare-rel/rule/query) scripts, which the
        // CHC engine decides with the correct (inverted) sat/unsat polarity.
        if is_fixedpoint_format(&content) {
            reject_bv_cnf_export_for_non_smt_route("fixedpoint stdin");
            chc_runner::run_chc_from_content(&content, verbose, validate, stats_cfg, proof_config);
            return;
        }

        // Standard DPLL(T) path. Drive the SAME per-command `CommandStream`
        // recovery as file input (`run_smt_file_content`) so a malformed or
        // unknown command prints a z3-style `(error "...")` and execution
        // CONTINUES (advertised `:error-behavior continued-execution`), instead
        // of the old whole-buffer `parse` that aborted the entire stream — and
        // dropped every later command, including `check-sat` — on the first
        // parse error. Keeps piped `-in` behavior identical to file input.
        run_smt_file_content_on_dedicated_stack(&content, stats_cfg, proof_config, visualization);
        return;
    }

    // Line-by-line mode: TTY interactive OR piped incremental (#5360).
    run_interactive_smt_stream(stdin.lock(), is_tty, stats_cfg, proof_config, visualization);
}

/// Drive SMT-LIB input command-by-command from `reader`, flushing stdout after
/// every response so a pipe or coprocess peer sees each verdict immediately.
///
/// This is the path z3's `-in` uses. Reaching it for piped input (not only for a
/// TTY or `--incremental`) is what lets a coprocess driver that holds stdin open
/// — Why3, Dafny, Boogie, an IDE — work instead of deadlocking on a read-to-EOF.
/// `is_tty` only controls whether the interactive prompt is printed.
fn run_interactive_smt_stream(
    mut reader: impl BufRead,
    is_tty: bool,
    stats_cfg: stats_output::StatsConfig,
    proof_config: Option<&ProofConfig>,
    visualization: Option<VisualizationFormat>,
) {
    if is_tty {
        safe_println!("{}", super::features::interactive_banner());
    }

    let mut stdout = io::stdout();
    let mut input_buffer = String::new();
    // Running 1-based line number of the first line still in `input_buffer`, so
    // errors report their true position in the whole session (z3's `-in` does not
    // reset the line counter per command). Advanced by the lines consumed each
    // time the buffer is parsed and cleared.
    let mut line_base = 1usize;
    // Linear-time completeness gate for the accumulation buffer (#inc-lra-parse).
    // Default on; `AY_INC_LINEAR_PARSE=0`/`off` restores parse-every-line.
    let linear_parse = std::env::var_os("AY_INC_LINEAR_PARSE")
        .map(|v| v != "0" && v != "off" && v != "false")
        .unwrap_or(true);
    let mut depth_scan = IncrementalDepth::default();
    let mut artifact_input = String::new();
    let mut executor = new_executor();
    let mut transcript = SmtTranscriptState::new();
    let mut formula_stats = FormulaStats::default();
    let mut smt_logic: Option<String> = None;
    // Rewrite synthesized non-Alethe configs to Alethe for SMT
    // (Finding A in the development design notes).
    let adapted = adapt_proof_config_for_smt(proof_config);
    if let Some(proof) = adapted.as_ref() {
        if proof.format != ProofFormat::Alethe {
            safe_eprintln!(
                "Error: proof file '{}' uses DRAT/LRAT/Lean4 format, but SMT-LIB mode requires Alethe output",
                proof.path
            );
            std::process::exit(1);
        }
        executor.set_produce_proofs(true);
        apply_default_proof_budget(&mut executor, proof);
    } else {
        // No proof can be emitted this session (`--no-proof` / `--z3-mode` /
        // competition mode): skip retaining a deep parsed-AST clone of every
        // assertion (proof surface-syntax alignment only — ~190 MB of a 318 MB
        // peak on a 6 MB QF_UF input, #rss-vs-z3). An in-script
        // `(set-option :produce-proofs true)` re-enables retention.
        executor.set_retain_parsed_assertions(false);
    }

    loop {
        exit_if_timed_out_with_transcript_context(&transcript);
        if is_tty {
            safe_print!("> ");
        }
        let _ = stdout.flush();

        let mut line = String::new();
        let read_result = reader.read_line(&mut line);
        match read_result {
            Ok(0) => break,
            Ok(_) => {}
            Err(e) => {
                safe_eprintln!("Error reading input: {e}");
                break;
            }
        }

        input_buffer.push_str(&line);

        // Linear completeness gate: while the buffer's top-level parens are
        // still open the command cannot be complete, so keep reading without
        // re-lexing the whole (potentially multi-megabyte) buffer. This is the
        // dominant cost on multi-line BMC asserts. See `IncrementalDepth`.
        if linear_parse {
            depth_scan.feed(&line);
            if depth_scan.depth > 0 {
                continue;
            }
        }

        match parse(&input_buffer) {
            Ok(commands) => {
                let command_sources = collect_command_sources_from_line(&input_buffer, line_base);
                line_base += input_buffer.matches('\n').count();
                artifact_input.push_str(&input_buffer);
                input_buffer.clear();
                depth_scan = IncrementalDepth::default();
                if smt_logic.is_none() {
                    smt_logic = logic_from_commands(&commands).map(str::to_owned);
                }
                for (cmd_index, cmd) in commands.iter().enumerate() {
                    set_current_command_source(&mut transcript, &command_sources, cmd_index);
                    formula_stats.observe_command(cmd);
                    if matches!(cmd, Command::Exit) {
                        maybe_print_success(&transcript);
                        maybe_explain(&mut executor);
                        maybe_visualize(&artifact_input, &mut executor, visualization);
                        if stats_cfg.any() {
                            print_smt_stats(&executor, Some(&formula_stats), stats_cfg);
                        }
                        maybe_write_minimal_decision_trace(&executor);
                        if let Some(proof) = adapted.as_ref() {
                            write_alethe_proof(
                                &executor,
                                proof,
                                ProofArtifactProblem::Text(&artifact_input),
                                ProofArtifactTheoryMetadata::smt_lib(
                                    smt_logic.as_deref(),
                                    Some(&formula_stats),
                                ),
                            );
                        }
                        cleanup_temp_proof(adapted.as_ref());
                        exit_if_transcript_had_recoverable_error(&transcript);
                        return;
                    }
                    execute_and_print(&mut executor, cmd, &mut transcript, true);
                    // Flush after each command so pipe consumers see responses
                    // immediately (stdout is block-buffered when piped).
                    let _ = stdout.flush();
                    exit_if_timed_out_with_transcript_context(&transcript);
                }
            }
            Err(e) => {
                let opens = input_buffer.matches('(').count();
                let closes = input_buffer.matches(')').count();
                if opens <= closes {
                    // Balanced (or over-closed) buffer that still fails to
                    // parse. `parse` is a pure function of the buffer, so
                    // re-parsing the unchanged text can never succeed — report
                    // the error we already have, mirroring file mode
                    // (`run_smt_file_content`): a recoverable `(error "...")`
                    // on the regular output channel, marked so the process
                    // still exits non-zero. Clear the per-command source first
                    // — it still points at the last successfully parsed
                    // command from a previous batch and would misattribute
                    // this error's position.
                    transcript.current_source = None;
                    print_recoverable_parse_error(&mut transcript, &e);
                    invalidate_export_after_malformed_decision(&input_buffer);
                    // SOUNDNESS: mirror file mode — a problem-contributing
                    // command (e.g. a malformed `assert`) was dropped, so a
                    // later check-sat must fail closed to `unknown` instead of
                    // answering on the incomplete remainder.
                    if parse_drop_contributes_to_problem(&input_buffer) {
                        transcript.mark_incomplete();
                    }
                    line_base += input_buffer.matches('\n').count();
                    input_buffer.clear();
                    depth_scan = IncrementalDepth::default();
                }
            }
        }
    }
    maybe_explain(&mut executor);
    if stats_cfg.any() {
        maybe_visualize(&artifact_input, &mut executor, visualization);
        print_smt_stats(&executor, Some(&formula_stats), stats_cfg);
    } else {
        maybe_visualize(&artifact_input, &mut executor, visualization);
    }
    maybe_write_minimal_decision_trace(&executor);
    if let Some(proof) = adapted.as_ref() {
        write_alethe_proof(
            &executor,
            proof,
            ProofArtifactProblem::Text(&artifact_input),
            ProofArtifactTheoryMetadata::smt_lib(smt_logic.as_deref(), Some(&formula_stats)),
        );
    }
    cleanup_temp_proof(adapted.as_ref());
    exit_if_transcript_had_recoverable_error(&transcript);
}

/// Diagnostic for input files the CLI classifies as solver inputs and routes
/// into `ay solve` (`looks_like_input_path_arg` / `inject_solve_subcommand` in
/// main.rs) but that `ay solve` cannot parse. Returns the redirect message —
/// pointing at the dedicated subcommand where one exists — or `None` when the
/// file may be SMT-LIB/DIMACS/CHC and normal content routing should proceed.
///
/// Must be consulted BEFORE the file is read or content-sniffed: `.qdimacs`
/// keeps a `p cnf` header (the DIMACS sniffer would misroute it to the plain
/// SAT solver, where quantifier lines break), and `.aig` is binary (a
/// `read_to_string` would die with a raw read error).
// False positive: `path` is explicitly ASCII-lowercased before the suffix
// checks, and multi-part suffixes like `.wcnf.xz` don't fit `Path::extension`.
#[allow(clippy::case_sensitive_file_extension_comparisons)]
fn dedicated_subcommand_redirect(path: &str) -> Option<&'static str> {
    let lower = path.to_ascii_lowercase();
    if lower.ends_with(".fzn") {
        Some("FlatZinc input is not supported by `ay solve`; use `ay flatzinc solve FILE`")
    } else if lower.ends_with(".qdimacs") {
        Some("QDIMACS (QBF) input is not supported by `ay solve`; use `ay qbf solve FILE`")
    } else if lower.ends_with(".wcnf") || lower.ends_with(".wcnf.xz") {
        Some("weighted CNF (MaxSAT) input is not supported by `ay solve`; use `ay maxsat solve FILE`")
    } else if lower.ends_with(".opb") {
        Some("OPB pseudo-Boolean input is not supported by `ay solve`; use `ay pb solve FILE`")
    } else if lower.ends_with(".mps") || lower.ends_with(".lp") {
        Some("MPS/CPLEX-LP input is not supported by `ay solve`; use `ay lp solve FILE`")
    } else if lower.ends_with(".aig") || lower.ends_with(".aag") {
        Some("AIGER input is not supported by `ay solve`")
    } else if lower.ends_with(".sl") {
        Some("SyGuS input is not supported by `ay solve`")
    } else {
        None
    }
}

pub(super) fn run_file(
    path: &str,
    stats_cfg: stats_output::StatsConfig,
    proof_config: Option<&ProofConfig>,
    parallel_threads: Option<usize>,
    cube_and_conquer_depth: Option<usize>,
    visualization: Option<VisualizationFormat>,
    verbose: bool,
    validate: bool,
) {
    // Known non-SMT input extensions get an explicit redirect to their
    // dedicated subcommand instead of a raw parse/read error.
    if let Some(redirect) = dedicated_subcommand_redirect(path) {
        safe_eprintln!("Error: {redirect}");
        std::process::exit(1);
    }

    if let Some(proof) = proof_config {
        if parallel_threads.is_none()
            && cube_and_conquer_depth.is_none()
            && dimacs::has_dimacs_file_extension(path)
        {
            reject_bv_cnf_export_for_non_smt_route("DIMACS file");
            dimacs::run_dimacs_proof_from_file(path, stats_cfg, proof);
            return;
        }
    }

    match std::fs::read_to_string(path) {
        Ok(content) => {
            // Check for DIMACS CNF format first (by extension or content)
            if dimacs::has_cnf_extension(path) || dimacs::is_dimacs_format(&content) {
                reject_bv_cnf_export_for_non_smt_route("DIMACS file");
                if dimacs::has_structural_sidecar(path)
                    && (cube_and_conquer_depth.is_some() || parallel_threads.is_some())
                {
                    safe_eprintln!(
                        "c structural-sidecar: adjacent sidecar present; using checked sequential DIMACS route"
                    );
                    dimacs::run_dimacs_from_file(path, &content, stats_cfg, proof_config);
                } else if let Some(depth) = cube_and_conquer_depth {
                    let num_threads = parallel_threads.unwrap_or_else(|| {
                        std::thread::available_parallelism()
                            .map(std::num::NonZero::get)
                            .unwrap_or(4)
                    });
                    dimacs::run_dimacs_cube_and_conquer(
                        &content,
                        stats_cfg,
                        proof_config,
                        depth,
                        num_threads,
                    );
                } else if let Some(num_threads) = parallel_threads {
                    dimacs::run_dimacs_parallel(&content, stats_cfg, proof_config, num_threads);
                } else {
                    dimacs::run_dimacs_from_file(path, &content, stats_cfg, proof_config);
                }
                return;
            }

            // Check for HORN logic and route to CHC solver if found
            if is_horn_logic(&content) {
                reject_bv_cnf_export_for_non_smt_route("CHC file");
                chc_runner::run_chc_from_content(
                    &content,
                    verbose,
                    validate,
                    stats_cfg,
                    proof_config,
                );
                return;
            }

            // Z3 fixedpoint (declare-rel/rule/query) scripts also route to the
            // CHC engine (correct inverted sat/unsat polarity handled there).
            if is_fixedpoint_format(&content) {
                reject_bv_cnf_export_for_non_smt_route("fixedpoint file");
                chc_runner::run_chc_from_content(
                    &content,
                    verbose,
                    validate,
                    stats_cfg,
                    proof_config,
                );
                return;
            }

            run_smt_file_content_on_dedicated_stack(
                &content,
                stats_cfg,
                proof_config,
                visualization,
            );
        }
        Err(e) => {
            eprintln_smt_error(format_args!("Error reading file '{path}': {e}"));
            std::process::exit(1);
        }
    }
}

fn run_smt_file_content_on_dedicated_stack(
    content: &str,
    stats_cfg: stats_output::StatsConfig,
    proof_config: Option<&ProofConfig>,
    visualization: Option<VisualizationFormat>,
) {
    std::thread::scope(|scope| {
        match std::thread::Builder::new()
            .name("ay-smt-file".to_string())
            .stack_size(SMT_FILE_THREAD_STACK_SIZE)
            .spawn_scoped(scope, move || {
                run_smt_file_content(content, stats_cfg, proof_config, visualization)
            }) {
            Ok(handle) => match handle.join() {
                Ok(()) => {}
                Err(payload) => std::panic::resume_unwind(payload),
            },
            Err(_) => run_smt_file_content(content, stats_cfg, proof_config, visualization),
        }
    });
}

fn run_smt_file_content(
    content: &str,
    stats_cfg: stats_output::StatsConfig,
    proof_config: Option<&ProofConfig>,
    visualization: Option<VisualizationFormat>,
) {
    // MILP FAST-PATH (#milp-fastpath): a QF_LRA script that is exactly a big-M
    // MILP feasibility problem — conjunctive linear rows plus 0/1 disjunctions,
    // the shape the downstream optimization consumer's mip-diff pipes in — is decided by ay-milp's branch-and-cut
    // instead of the generic DPLL(T) case-split, which produces no verdict on
    // real NN windows the MILP lane settles in minutes. Fail-closed: anything
    // outside the recognised fragment falls through to the standard lane
    // untouched, and the route is skipped when the caller asked for stats,
    // visualization, or an EXPLICIT `--proof` — the fast path cannot produce
    // Alethe. Solver-SYNTHESIZED proof configs do not block it — neither the
    // default certificate (`synthesized_default`, best-effort by design) nor
    // the `--verify-proof` temp path stdin input gets (`is_temp`; its
    // post-solve re-check and cleanup both no-op when no proof file was
    // produced): a fast-path `sat` needs no certificate, and a fast-path
    // `unsat` trades the best-effort certificate for a verdict the generic
    // lane cannot reach at all on this shape. Only a USER-requested `--proof`
    // keeps the standard lane unconditionally.
    let explicit_proof = proof_config.is_some_and(|p| !p.synthesized_default && !p.is_temp);
    if !explicit_proof
        && visualization.is_none()
        && !stats_cfg.human
        && !stats_cfg.json
        && crate::milp_fastpath::try_milp_fastpath(content)
    {
        return;
    }

    // Per-command error recovery (continued-execution) for FILE input.
    //
    // We drive the same parser internals as `parse`, but command-by-command via
    // `CommandStream`, so a malformed or unknown command no longer aborts the
    // whole file: we print a z3-style `(error "...")` and continue with the
    // remaining commands (advertised `:error-behavior continued-execution`).
    //
    // `formula_stats`/`smt_logic` are accumulated incrementally (as in the
    // interactive path) because we can no longer collect the full command list
    // up front — a bad command must not prevent stats/logic from the commands
    // that DID parse.
    let mut executor = new_executor();
    let mut transcript = SmtTranscriptState::new();
    let mut formula_stats = FormulaStats::default();
    let mut smt_logic: Option<String> = None;
    let command_sources = collect_command_sources(content);
    // Rewrite synthesized non-Alethe configs to Alethe for SMT
    // (Finding A in the development design notes).
    let adapted = adapt_proof_config_for_smt(proof_config);
    if let Some(proof) = adapted.as_ref() {
        if proof.format != ProofFormat::Alethe {
            safe_eprintln!(
                "Error: proof file '{}' uses DRAT/LRAT/Lean4 format, but SMT-LIB mode requires Alethe output",
                proof.path
            );
            std::process::exit(1);
        }
        executor.set_produce_proofs(true);
        apply_default_proof_budget(&mut executor, proof);
    } else {
        // No proof can be emitted this session (`--no-proof` / `--z3-mode` /
        // competition mode): skip retaining a deep parsed-AST clone of every
        // assertion (proof surface-syntax alignment only — ~190 MB of a 318 MB
        // peak on a 6 MB QF_UF input, #rss-vs-z3). An in-script
        // `(set-option :produce-proofs true)` re-enables retention.
        executor.set_retain_parsed_assertions(false);
    }

    let mut cmd_index = 0usize;
    let mut stream = CommandStream::new(content);
    loop {
        // Delimit the exact source slice this command consumes (used below to
        // classify a dropped command on a parse error, independent of the
        // possibly-misaligned `command_sources` re-chunking).
        let consumed_start = stream.position();
        let Some(item) = stream.next_command() else {
            break;
        };
        let consumed = content
            .get(consumed_start..stream.position())
            .unwrap_or_default();
        // Source tracking advances per top-level command (both successful and
        // failed ones occupy a slot), keeping positions aligned with the
        // balanced-paren chunks `collect_command_sources` recorded.
        set_current_command_source(&mut transcript, &command_sources, cmd_index);
        cmd_index += 1;
        match item {
            CommandStreamItem::Error(err) => {
                // z3-style continued-execution: report the bad command and keep
                // going. Marked recoverable so the process still exits non-zero.
                print_recoverable_parse_error(&mut transcript, &err);
                invalidate_export_after_malformed_decision(consumed);
                // SOUNDNESS: a problem-contributing command (e.g. an `assert`
                // using an unsupported construct) just failed to parse and was
                // dropped. Taint the session so a later check-sat fails closed to
                // `unknown` instead of answering on the incomplete remainder.
                if parse_drop_contributes_to_problem(consumed) {
                    transcript.mark_incomplete();
                }
                exit_if_timed_out_with_transcript_context(&transcript);
            }
            CommandStreamItem::Command(cmd) => {
                formula_stats.observe_command(&cmd);
                if smt_logic.is_none() {
                    smt_logic = logic_from_commands(std::slice::from_ref(&cmd)).map(str::to_owned);
                }
                match cmd {
                    Command::Exit => {
                        maybe_print_success(&transcript);
                        maybe_explain(&mut executor);
                        maybe_visualize(content, &mut executor, visualization);
                        if stats_cfg.any() {
                            print_smt_stats(&executor, Some(&formula_stats), stats_cfg);
                        }
                        maybe_write_minimal_decision_trace(&executor);
                        if let Some(proof) = adapted.as_ref() {
                            write_alethe_proof(
                                &executor,
                                proof,
                                ProofArtifactProblem::Text(content),
                                ProofArtifactTheoryMetadata::smt_lib(
                                    smt_logic.as_deref(),
                                    Some(&formula_stats),
                                ),
                            );
                        }
                        cleanup_temp_proof(adapted.as_ref());
                        exit_if_transcript_had_recoverable_error(&transcript);
                        return;
                    }
                    _ => {
                        if !execute_and_print(&mut executor, &cmd, &mut transcript, false) {
                            exit_if_timed_out_with_transcript_context(&transcript);
                            std::process::exit(1);
                        }
                    }
                }
                exit_if_timed_out_with_transcript_context(&transcript);
            }
        }
    }
    maybe_explain(&mut executor);
    maybe_visualize(content, &mut executor, visualization);
    if stats_cfg.any() {
        print_smt_stats(&executor, Some(&formula_stats), stats_cfg);
    }
    maybe_write_minimal_decision_trace(&executor);
    if let Some(proof) = adapted.as_ref() {
        write_alethe_proof(
            &executor,
            proof,
            ProofArtifactProblem::Text(content),
            ProofArtifactTheoryMetadata::smt_lib(smt_logic.as_deref(), Some(&formula_stats)),
        );
    }
    cleanup_temp_proof(adapted.as_ref());
    exit_if_transcript_had_recoverable_error(&transcript);
}

/// Report a per-command parse/elaboration error (z3 continued-execution).
///
/// Mirrors the recoverable execution-error path: the `(error "...")` line goes
/// to the regular output channel (z3 prints recoverable errors on stdout) with
/// the offending command's source position when available, and the transcript
/// is marked so the process still exits non-zero. Subsequent valid commands are
/// executed by the caller's loop.
fn print_recoverable_parse_error(state: &mut SmtTranscriptState, err: &ay_frontend::ParseError) {
    state.note_recoverable_error();
    // Use the offending command's *absolute* position from `command_sources`
    // (the parser's own line/column are relative to the per-command slice and
    // would be wrong for whole-file reporting). Emit only the bare error
    // `message` so the position is not duplicated by `ParseError`'s Display.
    let position = state.current_source.as_ref().map(|source| SourcePosition {
        line: source.line,
        column: source.column,
    });
    let line = source_error(position, &err.message);
    print_regular_line(state, &line);
}

/// Check if content uses HORN logic
pub(super) fn is_horn_logic(content: &str) -> bool {
    // Avoid parsing large non-HORN SMT-LIB inputs on the caller stack.
    if !content.contains("HORN") {
        return false;
    }
    if content.contains("(set-logic HORN)") {
        return true;
    }
    if let Ok(commands) = parse(content) {
        commands
            .iter()
            .any(|cmd| matches!(cmd, Command::SetLogic(logic) if logic == "HORN"))
    } else {
        // Fallback: simple string check for unparseable content
        content.contains("(set-logic HORN)")
    }
}

/// Detect a Z3 fixedpoint (relational / CHC) script.
///
/// z3 exposes its fixedpoint engine through `declare-rel` / `declare-var` /
/// `rule` / `query` commands, often WITHOUT `(set-logic HORN)`. Such a script
/// is a CHC problem and must be routed to the `ay-chc` engine, not the DPLL(T)
/// solver (which has no notion of relations/rules and would reject `rule` /
/// `query`).
///
/// Detection is precise: `rule` and `query` are not valid SMT-LIB commands in
/// any non-fixedpoint context, so their presence unambiguously identifies a
/// fixedpoint script. A bare `declare-rel` alone (without any `rule`/`query`)
/// is NOT treated as fixedpoint — without a query there is nothing to decide,
/// so we leave it to the normal path rather than risk misrouting.
///
/// SOUNDNESS: this only changes which engine runs; the CHC engine itself emits
/// `sat`/`unsat`/`unknown` soundly (with fixedpoint polarity already handled by
/// `ChcProblem::is_fixedpoint_format`). When in doubt we return `false` and let
/// the standard pipeline handle (and, if truly unsupported, reject) the input.
pub(super) fn is_fixedpoint_format(content: &str) -> bool {
    // Cheap pre-filter: a fixedpoint script must mention `rule` or `query`.
    // This token check avoids parsing large ordinary SMT-LIB inputs and is a
    // strict over-approximation of the precise parse-based check below.
    if !(content.contains("rule") || content.contains("query")) {
        return false;
    }
    let Ok(commands) = parse(content) else {
        return false;
    };
    // Require an actual fixedpoint command — a `rule` or `query`. `declare-rel`
    // alone does not constitute a decidable fixedpoint problem.
    commands
        .iter()
        .any(|cmd| matches!(cmd, Command::Rule(_) | Command::Query(_)))
}
