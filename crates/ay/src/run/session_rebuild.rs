// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `run` to preserve private helper paths and behavior.

/// One executor mutation recorded for [`SessionReplayLog`].
#[derive(Debug)]
enum SessionReplayStep {
    /// The source text of a command the executor accepted. It is recorded
    /// only after checking that the text parses back to exactly that command,
    /// so replay can never execute a misattributed source. `persistent` marks
    /// a command whose effect no `(pop)` undoes: `set-option`, `set-info`,
    /// `set-logic` and `dbg-set`.
    Authored { text: String, persistent: bool },
    /// The source text of an assertion rejected at one of its `:named`
    /// labels, which keeps the labels bound before that one. Replaying it has
    /// to be rejected the same way.
    RejectedAssertion { text: String },
    /// One assertion level, stored per level so a partial `(pop k)` of a
    /// `(push n)` keeps the levels that survive it.
    Push,
}

impl SessionReplayStep {
    /// Whether the step survives the `(pop)` of the level it was recorded in.
    fn outlives_pop(&self) -> bool {
        match self {
            Self::Authored { persistent, .. } => *persistent,
            Self::RejectedAssertion { .. } | Self::Push => false,
        }
    }
}

/// One open assertion level of [`SessionReplayLog`].
#[derive(Debug)]
struct SessionReplayLevel {
    /// Log length before the level's `Push` step.
    start: usize,
    /// Whether `:global-declarations` was in force at any time while the level
    /// was open. A declaration made then outlives the level's `(pop)`, so the
    /// level has to be replayed verbatim, `(pop)` included.
    saw_global_declarations: bool,
}

/// The executor mutations of the current `(reset)` epoch, in order.
///
/// z3 reports a failed command and keeps answering. A command that fails
/// inside the executor can leave it part-way through a mutation, so this
/// session does not keep using that executor: it builds a fresh one and
/// replays these steps. The fresh executor has the declarations, definitions,
/// assertions, assertion levels and options of a solver that never saw the
/// failed command. It does not have the live executor's check-sat history
/// (learned lemmas, adopted definitions, incremental solver state), so a
/// later query can come out more or less complete than it would have, never
/// with a different meaning. Pure queries (`check-sat`, `get-*`, `echo`, ...)
/// change no problem state and are not recorded.
///
/// A level closed by a `(pop)` is dropped from the log when every declaration
/// made in it was scoped, since the pop returns the problem to the state
/// before the matching push. The frontend decides a declaration's scope when
/// the declaration is made, so a level that was open while
/// `:global-declarations` was in force is kept, with its `(pop)`.
#[derive(Debug, Default)]
struct SessionReplayLog {
    steps: Vec<SessionReplayStep>,
    /// The open assertion levels, innermost last.
    levels: Vec<SessionReplayLevel>,
    /// The last `(set-option :rlimit N)`, which the transcript layer forwards
    /// to `Executor::apply_rlimit_option` instead of executing it. Only the
    /// last value matters because replay runs no query.
    rlimit: Option<String>,
}

impl SessionReplayLog {
    fn open_levels(&mut self, count: u32, global_declarations: bool) {
        for _ in 0..count {
            self.levels.push(SessionReplayLevel {
                start: self.steps.len(),
                saw_global_declarations: global_declarations,
            });
            self.steps.push(SessionReplayStep::Push);
        }
    }

    /// Close the innermost `count` levels. `false` when the log holds fewer
    /// open levels than that.
    fn close_levels(&mut self, count: u32) -> bool {
        let count = count as usize;
        if count > self.levels.len() {
            return false;
        }
        if count == 0 {
            return true;
        }
        let closed = self.levels.split_off(self.levels.len() - count);
        if closed.iter().any(|level| level.saw_global_declarations) {
            self.steps.push(SessionReplayStep::Authored {
                text: format!("(pop {count})"),
                persistent: false,
            });
        } else {
            // Options are not scoped by push/pop, so the ones set inside the
            // closed levels stay in force and stay in the log.
            let dropped = self.steps.split_off(closed[0].start);
            self.steps
                .extend(dropped.into_iter().filter(SessionReplayStep::outlives_pop));
        }
        true
    }
}

/// Whether the executor's frontend currently makes declarations global.
fn global_declarations_in_force(executor: &Executor) -> bool {
    matches!(
        executor.context().get_option("global-declarations"),
        Some(ay_frontend::OptionValue::Bool(true))
    )
}

/// Commands whose execution reads solver state without changing the problem.
fn command_is_pure_query(cmd: &Command) -> bool {
    matches!(
        cmd,
        Command::CheckSat
            | Command::CheckSatAssuming(_)
            | Command::CheckSynth
            | Command::GetModel
            | Command::GetObjectives
            | Command::GetObjectiveCertificates
            | Command::GetValue(_)
            | Command::Eval(_)
            | Command::GetConsequences(..)
            | Command::GetUnsatCore
            | Command::GetUnsatCoreWithFarkas
            | Command::GetUnsatAssumptions
            | Command::GetProof
            | Command::GetAssertions
            | Command::GetAssignment
            | Command::GetInfo(_)
            | Command::GetOption(_)
            | Command::Labels
            | Command::Echo(_)
            | Command::Display(..)
            | Command::Simplify(_)
            | Command::SimplifyWithParams(..)
            | Command::GetInterpolant(..)
            | Command::ComputeInterpolant(..)
            | Command::GetAbduct(..)
            | Command::Apply(_)
    )
}

/// Start keeping a replay log when a failed command may be survived: under
/// `--z3-mode`, and only when no proof, decision-trace or CNF artifact is being
/// written, since those transactions describe one executor's run.
fn enable_session_replay_if_supported(
    transcript: &mut SmtTranscriptState,
    proof: Option<&ProofConfig>,
) {
    let trace = ay_core::trace_config();
    if z3_mode_enabled()
        && proof.is_none()
        && trace.dump_bv_cnf_path.is_none()
        && trace.decision_trace_path.is_none()
    {
        transcript.continue_after_failure = true;
        transcript.replay_log = Some(SessionReplayLog::default());
    }
}

/// Record a command the executor has just accepted. `global_declarations` is
/// whether declarations are global once the command has run.
fn record_accepted_command(
    transcript: &mut SmtTranscriptState,
    cmd: &Command,
    global_declarations: bool,
) {
    let Some(log) = transcript.replay_log.as_mut() else {
        return;
    };
    if global_declarations {
        for level in &mut log.levels {
            level.saw_global_declarations = true;
        }
    }
    match cmd {
        Command::Reset => {
            log.steps.clear();
            log.levels.clear();
        }
        Command::Push(levels) => log.open_levels(*levels, global_declarations),
        Command::Pop(levels) => {
            if !log.close_levels(*levels) {
                // The executor accepted a pop the log cannot account for, so the
                // log no longer describes its state.
                transcript.replay_log = None;
            }
        }
        _ if command_is_pure_query(cmd) => {}
        _ => {
            if matches!(cmd, Command::ResetAssertions) {
                // Every assertion level is closed; later pops have nothing to undo.
                log.levels.clear();
            }
            let text = replayable_source_text(transcript, cmd);
            let Some(log) = transcript.replay_log.as_mut() else {
                return;
            };
            match text {
                Some(text) => log.steps.push(SessionReplayStep::Authored {
                    text,
                    persistent: matches!(
                        cmd,
                        Command::SetOption(..)
                            | Command::SetOptionAttribute(_)
                            | Command::SetInfo(..)
                            | Command::SetInfoAttribute(_)
                            | Command::SetLogic(_)
                            | Command::DebugSet(..)
                    ),
                }),
                None => transcript.replay_log = None,
            }
        }
    }
}

/// The source text of `cmd` when it parses back to exactly `cmd`.
fn replayable_source_text(transcript: &SmtTranscriptState, cmd: &Command) -> Option<String> {
    transcript
        .current_source
        .as_ref()
        .map(|source| source.text.as_str())
        .filter(|text| {
            parse(text).is_ok_and(|parsed| parsed.as_slice() == std::slice::from_ref(cmd))
        })
        .map(str::to_string)
}

/// Record an assertion rejected at a `:named` label after binding earlier
/// labels. `global_declarations` is whether declarations are global.
fn record_rejected_assertion(
    transcript: &mut SmtTranscriptState,
    cmd: &Command,
    global_declarations: bool,
) {
    let text = replayable_source_text(transcript, cmd);
    let Some(log) = transcript.replay_log.as_mut() else {
        return;
    };
    if global_declarations {
        for level in &mut log.levels {
            level.saw_global_declarations = true;
        }
    }
    match text {
        Some(text) => log
            .steps
            .push(SessionReplayStep::RejectedAssertion { text }),
        None => transcript.replay_log = None,
    }
}

/// Record assertion levels the session opened in the executor on its own.
fn record_opened_levels(
    transcript: &mut SmtTranscriptState,
    count: u32,
    global_declarations: bool,
) {
    if let Some(log) = transcript.replay_log.as_mut() {
        log.open_levels(count, global_declarations);
    }
}

/// Record an option the session set in the executor on its own. `text` must
/// be the exact command that was executed.
fn record_session_option(transcript: &mut SmtTranscriptState, text: &str) {
    if let Some(log) = transcript.replay_log.as_mut() {
        log.steps.push(SessionReplayStep::Authored {
            text: text.to_string(),
            persistent: true,
        });
    }
}

fn record_rlimit_option(transcript: &mut SmtTranscriptState, numeral: &str) {
    if let Some(log) = transcript.replay_log.as_mut() {
        log.rlimit = Some(numeral.to_string());
    }
}

/// Apply one recorded step to `executor`. `false` when it does not apply
/// exactly as it did the first time.
fn replay_session_step(executor: &mut Executor, step: &SessionReplayStep) -> bool {
    match step {
        SessionReplayStep::Authored { text, .. } => match parse(text).as_deref() {
            Ok([cmd]) => executor.execute_authored(cmd).is_ok(),
            _ => false,
        },
        SessionReplayStep::RejectedAssertion { text } => match parse(text).as_deref() {
            Ok([cmd]) => {
                executor.execute_authored(cmd).is_err()
                    && executor.context_mut().take_label_failure()
                        == Some(ay_frontend::LabelFailure::Exact)
            }
            _ => false,
        },
        SessionReplayStep::Push => executor.execute_authored(&Command::Push(1)).is_ok(),
    }
}

/// Build a fresh executor from the replay log, or `None` when there is no log
/// or a step does not replay cleanly.
fn rebuild_executor_from_replay_log(
    transcript: &SmtTranscriptState,
    make_executor: &dyn Fn() -> Executor,
) -> Option<Executor> {
    let log = transcript.replay_log.as_ref()?;
    std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let mut fresh = make_executor();
        if !log
            .steps
            .iter()
            .all(|step| replay_session_step(&mut fresh, step))
        {
            return None;
        }
        if let Some(numeral) = &log.rlimit {
            fresh.apply_rlimit_option(numeral);
        }
        Some(fresh)
    }))
    .ok()
    .flatten()
}

/// Keep the session going after `execute_and_print` reported a failure it
/// could not recover from, as z3 does. Returns `false` when the session must
/// end as before: outside `--z3-mode`, with an artifact being written, or
/// under `:exit-on-error`.
///
/// The failed command's output (an `unknown` for a query, the error where z3
/// would print one; see [`report_failure_in_surviving_session`]) has already
/// been printed. The executor is rebuilt without the failed command;
/// if that command could change the problem it counts as dropped, exactly as a
/// recoverable elaboration failure does. When the rebuild is impossible (the
/// log was given up, or a step does not replay) the executor is kept but the
/// session is marked incomplete, so no later `check-sat` publishes a verdict
/// from state the failure may have corrupted.
fn continue_after_failed_command(
    executor: &mut Executor,
    cmd: &Command,
    transcript: &mut SmtTranscriptState,
    make_executor: &dyn Fn() -> Executor,
) -> bool {
    if !session_survives_failures(transcript) {
        return false;
    }
    if !std::mem::take(&mut transcript.failure_reported) {
        transcript.note_recoverable_error();
    }
    if let Some(fresh) = rebuild_executor_from_replay_log(transcript, make_executor) {
        *executor = fresh;
        if command_contributes_to_problem(cmd) {
            if matches!(cmd, Command::Assert(_)) {
                mark_problem_incomplete_from_dropped_assertion(executor, transcript);
            } else {
                mark_problem_incomplete(executor, transcript);
            }
        }
        return true;
    }
    transcript.replay_log = None;
    // Marking the problem incomplete clears the public result; a failed query
    // keeps its `unknown` and reason for `(get-info :reason-unknown)`.
    let failed_query_reason = matches!(cmd, Command::CheckSat | Command::CheckSatAssuming(_))
        .then(|| transcript.public_unknown_reason.clone())
        .flatten();
    mark_problem_incomplete(executor, transcript);
    if let Some(reason) = failed_query_reason {
        transcript.record_synthesized_unknown(reason);
    }
    true
}

/// Whether a command that fails inside the executor leaves the session
/// running; see [`continue_after_failed_command`].
fn session_survives_failures(transcript: &SmtTranscriptState) -> bool {
    transcript.continue_after_failure && !transcript.exit_on_error
}

#[cfg(test)]
mod session_replay_tests {
    use super::*;

    /// Run `script` through an executor command by command, recording each
    /// accepted command the way the session loops do.
    fn record_script(script: &str) -> (Executor, SmtTranscriptState) {
        let mut executor = Executor::new();
        let mut transcript = SmtTranscriptState::new();
        transcript.replay_log = Some(SessionReplayLog::default());
        for item in read_stdin_commands(script, 1, 1) {
            let StdinCommand::Parsed(cmd, source) = item else {
                panic!("script parses");
            };
            let cmd = &*cmd;
            set_current_source(&mut transcript, source);
            executor.execute_authored(cmd).expect("command is accepted");
            let global = global_declarations_in_force(&executor);
            record_accepted_command(&mut transcript, cmd, global);
        }
        (executor, transcript)
    }

    fn rebuild(transcript: &SmtTranscriptState) -> Executor {
        rebuild_executor_from_replay_log(transcript, &Executor::new).expect("log replays")
    }

    fn logged_texts(transcript: &SmtTranscriptState) -> Vec<String> {
        let log = transcript.replay_log.as_ref().expect("log kept");
        log.steps
            .iter()
            .map(|step| match step {
                SessionReplayStep::Authored { text, .. }
                | SessionReplayStep::RejectedAssertion { text } => text.clone(),
                SessionReplayStep::Push => "(push)".to_string(),
            })
            .collect()
    }

    #[test]
    fn a_popped_scoped_level_is_dropped_from_the_log() {
        let (_, transcript) = record_script(
            "(declare-const x Int)\n(push)\n(define-fun five () Int 5)\n(assert (= x five))\n(pop)\n",
        );
        assert_eq!(logged_texts(&transcript), ["(declare-const x Int)"]);
        let mut rebuilt = rebuild(&transcript);
        assert!(!rebuilt.context_mut().has_symbol_binding("five"));
    }

    /// A declaration made while `:global-declarations` was on outlives the
    /// pop even when the option is off by the time of the pop, so the rebuilt
    /// executor must still know it.
    #[test]
    fn a_level_open_under_global_declarations_is_replayed_verbatim() {
        let script = "(set-option :global-declarations true)\n(push)\n\
                      (define-fun five () Int 5)\n(set-option :global-declarations false)\n\
                      (pop)\n";
        let (mut live, transcript) = record_script(script);
        assert!(live.context_mut().has_symbol_binding("five"));
        assert!(logged_texts(&transcript)
            .iter()
            .any(|text| text == "(pop 1)"));
        let mut rebuilt = rebuild(&transcript);
        assert!(rebuilt.context_mut().has_symbol_binding("five"));
        assert!(!global_declarations_in_force(&rebuilt));
    }

    #[test]
    fn set_logic_and_options_survive_the_pop_of_their_level() {
        let (_, transcript) = record_script(
            "(push)\n(set-logic QF_LIA)\n(set-option :produce-models true)\n\
             (declare-const x Int)\n(pop)\n",
        );
        assert_eq!(
            logged_texts(&transcript),
            ["(set-logic QF_LIA)", "(set-option :produce-models true)"]
        );
        rebuild(&transcript);
    }

    #[test]
    fn a_pop_of_zero_levels_changes_nothing() {
        let (_, transcript) = record_script("(push)\n(declare-const x Int)\n(pop 0)\n");
        assert_eq!(
            logged_texts(&transcript),
            ["(push)", "(declare-const x Int)"]
        );
    }
}
