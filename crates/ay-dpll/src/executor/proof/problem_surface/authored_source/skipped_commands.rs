// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The commands pinned Carcara's `parse_problem` (`carcara/src/parser/mod.rs`
//! at 9a352ee) skips: any command whose keyword is not one of its reserved
//! words is read token by token to its closing parenthesis (its lexer still
//! runs over it, see `lexer`).

use ay_frontend::Command;

/// Commands Carcara's `parse_problem` skips token by token. None introduces a
/// symbol a later command uses.
pub(super) fn carcara_skips(command: &Command) -> bool {
    matches!(
        command,
        Command::SetOption(..)
            | Command::SetOptionAttribute(_)
            | Command::SetInfo(..)
            | Command::SetInfoAttribute(_)
            | Command::CheckSat
            | Command::AssertSoft { .. }
            | Command::Maximize(_)
            | Command::Minimize(_)
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
            | Command::Push(_)
            | Command::Pop(_)
            | Command::Reset
            | Command::ResetAssertions
            | Command::Exit
            | Command::Echo(_)
            | Command::Display(..)
            | Command::DebugSet(..)
            | Command::DebugPpVar(_)
            | Command::Simplify(_)
            | Command::SimplifyWithParams(..)
            | Command::GetInterpolant(..)
            | Command::ComputeInterpolant(..)
            | Command::GetAbduct(..)
            | Command::Apply(_)
    )
}
