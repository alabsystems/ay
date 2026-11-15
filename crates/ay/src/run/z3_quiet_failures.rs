// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `run` to preserve private helper paths and behavior.

// How a `--z3-mode` session reports a command that failed inside the
// executor: the way z3 would, with nothing on stderr.

/// Report the failure of a command `execute_and_print` could not recover
/// from: as z3 would in a session that survives it
/// ([`report_failure_in_surviving_session`]), else on stderr.
fn report_executor_failure(transcript: &mut SmtTranscriptState, cmd: &Command, message: String) {
    if session_survives_failures(transcript) {
        report_failure_in_surviving_session(transcript, cmd, &message);
    } else {
        // An `(error ...)` was printed: record it so the run's exit status
        // follows the printed-error rule even when the session continues
        // past the failure (continued-execution for decision queries).
        transcript.note_recoverable_error();
        eprintln_smt_error(message);
    }
}

/// Report a problem-contributing command dropped without ending the session
/// (an unbounded `define-fun-rec` expansion): nothing under `--z3-mode`,
/// where z3 reports no error, else on stderr.
fn report_dropped_command_error(
    transcript: &mut SmtTranscriptState,
    cmd: &Command,
    message: String,
) {
    if z3_mode_enabled() {
        keep_discarded_command_error(transcript, cmd, &message);
    } else {
        eprintln_smt_error(message);
    }
}

/// The reason of the `unknown` a discarded command forces, naming the
/// unprinted error when there is one.
fn discarded_command_reason(transcript: &SmtTranscriptState) -> String {
    match &transcript.discarded_command_error {
        Some(error) => smt_quoted_reason_detail(&format!(
            "a problem-contributing command was discarded: {error}"
        )),
        None => "\"a problem-contributing command was discarded\"".to_string(),
    }
}

/// Report a command that failed inside the executor, in a session that
/// survives the failure, the way z3 reports it: nothing on stderr.
///
/// z3 writes nothing to stderr during a normal session, and Verus's test
/// harness fails a test on any stderr line that is not one of its JSON
/// diagnostics. An input error reaches the executor as an elaboration error,
/// which `maybe_handle_recoverable_execution_error` has already printed on the
/// regular channel as z3 prints it. What reaches here is a limit of ay's (a
/// theory mix with no combined decision procedure, an internal solver error),
/// where z3 prints no error:
/// - a decision query has its `unknown`, and `(get-info :reason-unknown)`
///   carries the error;
/// - any other query owes a response and gets the one z3 gives to a query it
///   cannot answer, `(error ...)` on the regular channel;
/// - any other command prints nothing, and the `unknown` that its loss forces
///   later carries the error.
///
/// Only a printed `(error ...)` counts toward the exit status, since z3 exits 1
/// exactly when it printed one.
fn report_failure_in_surviving_session(
    transcript: &mut SmtTranscriptState,
    cmd: &Command,
    message: &str,
) {
    transcript.failure_reported = true;
    if matches!(cmd, Command::CheckSat | Command::CheckSatAssuming(_)) {
        note_unprinted_failure(transcript);
    } else if command_is_pure_query(cmd) {
        let position = current_source_last_token_position(transcript);
        print_regular_line(transcript, &source_error(position, message));
        transcript.note_recoverable_error();
    } else {
        keep_discarded_command_error(transcript, cmd, message);
    }
}

/// Record a failure that was not printed. It withholds artifacts as a printed
/// error does, but does not decide the exit status.
fn note_unprinted_failure(transcript: &mut SmtTranscriptState) {
    transcript.had_recoverable_error = true;
    transcript.recoverable_error_count = transcript.recoverable_error_count.saturating_add(1);
}

/// Under `--z3-mode`, keep the error of a dropped command that is not printed,
/// for the reason of the `unknown` its loss forces. The first one is kept: it
/// is the one that made the problem incomplete, until `(reset)`.
fn keep_discarded_command_error(transcript: &mut SmtTranscriptState, cmd: &Command, message: &str) {
    note_unprinted_failure(transcript);
    if command_contributes_to_problem(cmd) && transcript.discarded_command_error.is_none() {
        transcript.discarded_command_error = Some(message.to_string());
    }
}
