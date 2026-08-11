// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Large-stack execution boundary for the recursive counter.

use crate::output::SolveOutcome;
use crate::parse::{Instance, ProblemType};
use crate::{solve_instance, SolveOptions};

/// Solve on a dedicated thread with a large stack (the counting recursion is
/// as deep as the variable count in the worst case).
pub fn solve_instance_big_stack(instance: Instance, options: SolveOptions) -> SolveOutcome {
    const STACK_BYTES: usize = 1 << 30;
    let ptype = instance.ptype;
    let fallback_warnings = instance.warnings.clone();
    let handle = match std::thread::Builder::new()
        .name("ay-count".into())
        .stack_size(STACK_BYTES)
        .spawn(move || solve_instance(&instance, &options))
    {
        Ok(handle) => handle,
        Err(error) => {
            return thread_failure(
                ptype,
                fallback_warnings,
                format!("could not start counting thread: {error}"),
            );
        }
    };
    match handle.join() {
        Ok(outcome) => outcome,
        Err(_) => thread_failure(
            ptype,
            fallback_warnings,
            "counting thread terminated unexpectedly".to_string(),
        ),
    }
}

fn thread_failure(ptype: ProblemType, mut warnings: Vec<String>, message: String) -> SolveOutcome {
    warnings.push(message);
    SolveOutcome {
        ptype,
        satisfiable: None,
        value: None,
        warnings,
        stats: None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn failures_are_reported_as_unknown() {
        let outcome = thread_failure(
            ProblemType::Mc,
            vec!["existing warning".to_string()],
            "thread failed".to_string(),
        );
        assert_eq!(outcome.ptype, ProblemType::Mc);
        assert_eq!(outcome.satisfiable, None);
        assert_eq!(outcome.value, None);
        assert_eq!(outcome.warnings, ["existing warning", "thread failed"]);
    }
}
