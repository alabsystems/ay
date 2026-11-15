// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `run` to preserve private helper paths and behavior.

/// No recorded solver work before the session starts. Reset creates a new
/// counter; reset-assertions preserves cumulative work. Z3's numeric work
/// units are implementation details, not values AY should imitate.
const INITIAL_RLIMIT_COUNT: u64 = 0;

fn update_rlimit_after_command(state: &mut SmtTranscriptState, cmd: &Command) {
    if matches!(cmd, Command::Reset) {
        state.rlimit = INITIAL_RLIMIT_COUNT;
    }
}

/// Accumulate actual recorded solver work, including failed commands. The
/// transcript survives executor rebuilding and must never decrease on it.
fn charge_rlimit_work(state: &mut SmtTranscriptState, work: u64) {
    state.rlimit = state.rlimit.saturating_add(work);
}

/// Run `cmd` in the executor, containing a panic, and charge the solver work
/// it recorded, whatever the outcome.
fn execute_charging_rlimit(
    executor: &mut Executor,
    cmd: &Command,
    transcript: &mut SmtTranscriptState,
) -> std::thread::Result<ay_dpll::ExecutorResult<Option<String>>> {
    let work_before = executor.rlimit_work_total();
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        executor.execute_authored(cmd)
    }));
    let work = executor.rlimit_work_total().saturating_sub(work_before);
    charge_rlimit_work(transcript, work);
    result
}

/// The executor's statistics for `-st`, with the session's resource counter
/// as `:rlimit-count`, as `(get-info :all-statistics)` reports it.
fn statistics_with_session_rlimit(
    executor: &Executor,
    transcript: &SmtTranscriptState,
) -> ay_dpll::Statistics {
    let mut statistics = executor.statistics().clone();
    statistics.rlimit_count = transcript.rlimit;
    statistics
}

/// The executor's `(get-info :all-statistics)` with the session's resource
/// counter as its `:rlimit-count`: the executor reports the work of its last
/// check-sat there, which starts again at every check-sat and at every rebuild.
fn with_session_rlimit_count(statistics: &str, rlimit: u64) -> String {
    let lines: Vec<String> = statistics
        .split('\n')
        .map(|line| {
            let value = line
                .trim_start_matches(['(', ' '])
                .strip_prefix(":rlimit-count ")
                .map(str::trim_start);
            let digits = value.map_or(0, |value| {
                value.bytes().take_while(u8::is_ascii_digit).count()
            });
            match value {
                Some(value) if digits > 0 => format!(
                    "{}{rlimit}{}",
                    &line[..line.len() - value.len()],
                    &value[digits..]
                ),
                _ => line.to_string(),
            }
        })
        .collect();
    lines.join("\n")
}

#[cfg(test)]
mod session_rlimit_tests {
    use super::*;

    #[test]
    fn commands_report_executor_work_without_synthetic_minima() {
        let mut executor = Executor::new();
        let mut state = SmtTranscriptState::new();
        let commands =
            parse("(set-logic QF_LIA) (declare-const x Int) (assert (= x 1)) (check-sat)")
                .expect("valid commands");
        for command in commands {
            let before = executor.rlimit_work_total();
            let reported = state.rlimit;
            assert!(matches!(
                execute_charging_rlimit(&mut executor, &command, &mut state),
                Ok(Ok(_))
            ));
            update_rlimit_after_command(&mut state, &command);
            assert_eq!(
                state.rlimit - reported,
                executor.rlimit_work_total() - before,
                "{command:?}: telemetry must report actual recorded work"
            );
        }
    }

    #[test]
    fn resource_counter_cannot_wrap_and_break_unsigned_consumer_deltas() {
        let mut state = SmtTranscriptState::new();
        charge_rlimit_work(&mut state, u64::MAX);
        charge_rlimit_work(&mut state, 1);
        assert_eq!(
            state.rlimit,
            u64::MAX,
            "overflow must not decrease a reading"
        );
    }

    /// Reset-assertions preserves work; only reset starts a new session count.
    #[test]
    fn reset_starts_the_counter_again_and_reset_assertions_does_not() {
        let mut state = SmtTranscriptState::new();
        charge_rlimit_work(&mut state, 4_000);
        update_rlimit_after_command(&mut state, &Command::CheckSat);
        let before = state.rlimit;
        update_rlimit_after_command(&mut state, &Command::ResetAssertions);
        assert_eq!(state.rlimit, before);
        charge_rlimit_work(&mut state, 0);
        update_rlimit_after_command(&mut state, &Command::Reset);
        assert_eq!(state.rlimit, INITIAL_RLIMIT_COUNT);
    }

    #[test]
    fn the_executor_statistics_carry_the_session_counter() {
        let executor_output = "(:conflicts    0\n :num-clauses  2\n :rlimit-count 11\n \
                               :time         0.22)";
        assert_eq!(
            with_session_rlimit_count(executor_output, 4_321),
            "(:conflicts    0\n :num-clauses  2\n :rlimit-count 4321\n :time         0.22)"
        );
        // First and last line of the s-expression, and no line to rewrite.
        assert_eq!(
            with_session_rlimit_count("(:rlimit-count 7)", 90),
            "(:rlimit-count 90)"
        );
        assert_eq!(
            with_session_rlimit_count("(:conflicts 0\n :rlimit-count  0)", 5),
            "(:conflicts 0\n :rlimit-count  5)"
        );
        assert_eq!(with_session_rlimit_count("(:time 0.10)", 5), "(:time 0.10)");
        assert_eq!(
            with_session_rlimit_count("(:rlimit-counter 3)", 5),
            "(:rlimit-counter 3)"
        );
    }
}
