// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `(set-option :check-proofs-strict true)`: the ONE reading of the in-script
//! strict-proofs request.
//!
//! The executor reads it from its live [`Context`]
//! ([`Context::check_proofs_strict_requested`]). A route that never gives the
//! script to an executor — the CHC engine parses HORN and fixedpoint scripts
//! itself and skips every `set-option` — reads the SAME option through
//! [`script_requests_strict_proofs`], which replays the script's option
//! commands on a fresh [`Context`]. So a spelling the executor treats as strict
//! (or not) is treated the same way by every route: there is no second parser
//! of the option value to drift.

use super::{Context, OptionValue};
use crate::command::Command;
use crate::parser::{CommandStream, CommandStreamItem};

/// The option keyword, without its leading `:`.
const CHECK_PROOFS_STRICT: &str = "check-proofs-strict";

impl Context {
    /// Whether `(set-option :check-proofs-strict true)` is in force.
    ///
    /// Only the Boolean `true` counts, exactly as for every other Boolean
    /// option; `(reset)` clears it.
    #[must_use]
    pub fn check_proofs_strict_requested(&self) -> bool {
        matches!(
            self.get_option(CHECK_PROOFS_STRICT),
            Some(OptionValue::Bool(true))
        )
    }
}

/// Whether `script` asks for strict proofs with `:check-proofs-strict`.
///
/// The script is read command by command, the way a session executes it (a
/// malformed command is skipped, not fatal). Its `set-option` and `(reset)`
/// commands are applied to a fresh [`Context`], and the answer is `true` when
/// [`Context::check_proofs_strict_requested`] holds at any decision command
/// (`check-sat`, `check-sat-assuming`, fixedpoint `query`) or at the end of
/// the script. A route that decides the whole script as one problem (the CHC
/// engine) therefore runs strict whenever any of its decisions would be
/// strict in a session; the only error this direction can make is to be
/// strict where a session would not be.
#[must_use]
pub fn script_requests_strict_proofs(script: &str) -> bool {
    // A keyword cannot be quoted or escaped, so a script that never spells the
    // option cannot set it. This keeps the large CHC inputs that do not use
    // the option free of a second parse.
    if !script.contains(CHECK_PROOFS_STRICT) {
        return false;
    }
    let mut ctx = Context::new();
    let mut stream = CommandStream::new(script);
    while let Some(item) = stream.next_command() {
        let CommandStreamItem::Command(command) = item else {
            continue;
        };
        match *command {
            Command::SetOption(..) | Command::Reset => {
                // A rejected option leaves the option table as it was, which is
                // what the executor does with the same command.
                let _ = ctx.process_command(&command);
            }
            Command::CheckSat | Command::CheckSatAssuming(_) | Command::Query(_)
                if ctx.check_proofs_strict_requested() =>
            {
                return true;
            }
            _ => {}
        }
    }
    ctx.check_proofs_strict_requested()
}

#[cfg(test)]
mod tests {
    use super::script_requests_strict_proofs;

    const HORN: &str = "(set-logic HORN)\n(declare-fun inv (Int) Bool)\n\
        (assert (forall ((x Int)) (=> (= x 0) (inv x))))\n\
        (assert (forall ((x Int)) (=> (and (inv x) (> x 5)) false)))\n";

    #[test]
    fn the_option_set_before_the_decision_is_strict() {
        let script = format!("(set-option :check-proofs-strict true)\n{HORN}(check-sat)\n");
        assert!(script_requests_strict_proofs(&script));
    }

    #[test]
    fn the_option_set_after_the_logic_is_strict() {
        let script = format!("{HORN}(set-option :check-proofs-strict true)\n(check-sat)\n");
        assert!(script_requests_strict_proofs(&script));
    }

    #[test]
    fn a_fixedpoint_query_is_a_decision() {
        let script = "(set-option :check-proofs-strict true)\n(declare-rel r (Int))\n\
            (declare-var x Int)\n(rule (=> (= x 0) (r x)))\n(query r)\n\
            (set-option :check-proofs-strict false)\n";
        assert!(script_requests_strict_proofs(script));
    }

    #[test]
    fn the_option_in_force_only_after_the_last_decision_is_still_strict() {
        let script = format!("{HORN}(check-sat)\n(set-option :check-proofs-strict true)\n");
        assert!(script_requests_strict_proofs(&script));
    }

    #[test]
    fn scripts_without_the_option_or_with_it_off_are_not_strict() {
        assert!(!script_requests_strict_proofs(&format!(
            "{HORN}(check-sat)\n"
        )));
        assert!(!script_requests_strict_proofs(&format!(
            "(set-option :check-proofs-strict false)\n{HORN}(check-sat)\n"
        )));
        assert!(!script_requests_strict_proofs(&format!(
            "(set-option :check-proofs-strict true)\n(reset)\n{HORN}(check-sat)\n"
        )));
        // The keyword inside a comment or a string is not the option.
        assert!(!script_requests_strict_proofs(&format!(
            "; :check-proofs-strict true\n(set-info :source |:check-proofs-strict true|)\n\
             {HORN}(check-sat)\n"
        )));
    }

    #[test]
    fn a_malformed_command_does_not_hide_a_later_option() {
        let script = format!(
            "(not-a-command 1 2)\n(set-option :check-proofs-strict true)\n{HORN}(check-sat)\n"
        );
        assert!(script_requests_strict_proofs(&script));
    }
}
